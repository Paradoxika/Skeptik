package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

abstract class Split
extends (Proof[N] => Proof[N]) {
  
  def selectVariable(proof: Proof[N]): E
  
  def split(proof: Proof[N], selectedVariable: E): (N,N) = {
    proof foldDown { (node: N, fixedPremises: Seq[(N,N)]) => 
      lazy val (fixedLeftPos,  fixedLeftNeg)  = fixedPremises.head;
      lazy val (fixedRightPos, fixedRightNeg) = fixedPremises.last;
      node match {
        case Axiom(conclusion) => (node,node)
        case CutIC(_,_,aux,_) if aux == selectedVariable => (fixedLeftPos, fixedRightNeg)

        case CutIC(left,right,aux,_) if (fixedLeftPos eq fixedLeftNeg) && (fixedRightPos eq fixedRightNeg) =>
          // I think this case is redundant with the following one and then useless :
          // Neg and Pos being equals implies they're equals to node's premises.
          // Keep the println until it shows something.
          val newNode = if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node
                        else { println("yooups") ; CutIC(fixedLeftPos, fixedRightPos, _ == aux, true) }
          (newNode, newNode)

        case CutIC(left,right,aux,_) =>
          ( if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node else CutIC(fixedLeftPos, fixedRightPos, _ == aux, true),
            if ((left eq fixedLeftNeg) && (right eq fixedRightNeg)) node else CutIC(fixedLeftNeg, fixedRightNeg, _ == aux, true) )
        
        case _ => (node, node)
      }
    }
  }
  
  def applyOnce(p: Proof[N]): Proof[N] = {
    val selectedVariable = selectVariable(p)
    val (left, right) = split(p, selectedVariable)
    CutIC(left, right, _ == selectedVariable)
  }
}


trait AdditivityHeuristic
extends Split  {
  protected def computeAdditivities(proof: Proof[N]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[E,Long]()
    def visit(node: N) = node match {
      case CutIC(_,_,aux,_) =>
        val nodeAdditivity = ((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1
        totalAdditivity += nodeAdditivity
        literalAdditivity.update(aux, literalAdditivity.getOrElse(aux,0.toLong) + nodeAdditivity)
      case _ =>
    }
    proof.foreach(visit)
    (literalAdditivity, totalAdditivity)
  }

  protected def chooseVariable(literalAdditivity: scala.collection.Map[E,Long], totalAdditivity: Long):E
  
  
  def selectVariable(proof: Proof[N]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    chooseVariable(literalAdditivity, totalAdditivity)
  }
}

object CottonSplit
extends Split with AdditivityHeuristic with RandomChoice

abstract class BoudouSplit
extends Split with AdditivityHeuristic {
  override def applyOnce(proof: Proof[N]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    def repeat(sum: Long):Proof[N] = {
      val selectedVariable = chooseVariable(literalAdditivity, sum)
      val (left, right) = split(proof, selectedVariable)
      val compressedProof: Proof[N] = CutIC(left, right, _ == selectedVariable)
      if (compressedProof.size < proof.size) compressedProof
      else {
        val newSum = sum - literalAdditivity(selectedVariable)
        if (newSum < 1) proof else {
          literalAdditivity.remove(selectedVariable)
          repeat(newSum)
        }
      }
    }
    repeat(totalAdditivity)
  }
}

object DeterministicBoudouSplit
extends BoudouSplit with DeterministicChoice

object RandomBoudouSplit
extends BoudouSplit with RandomChoice



trait RandomChoice
extends AdditivityHeuristic {
  private val rand = new scala.util.Random()

  private def randomLong(max: Long):Long = {
    if (max <= Int.MaxValue.toLong)
      rand.nextInt(max.toInt)
    else {
      var draw = rand.nextLong()
      if (draw < 0) draw = -draw
      if (draw < max) draw else ((draw - max).toDouble * max.toDouble / (Long.MaxValue - max).toDouble).toLong
    }
  }

  protected def chooseVariable(literalAdditivity: scala.collection.Map[E,Long], totalAdditivity: Long) = {
    val iterator = literalAdditivity.toIterator
    def searchPos(left: Long):E = {
      val next = iterator.next
      if (next._2 < left && iterator.hasNext) searchPos(left - next._2) else next._1
    }
    searchPos(randomLong(totalAdditivity) + 1)
  }
}

trait DeterministicChoice
extends AdditivityHeuristic {
  protected def chooseVariable(literalAdditivity: scala.collection.Map[E,Long], totalAdditivity: Long) = {
    val iterator = literalAdditivity.toIterator
    var (result, max) = iterator.next
    var left = totalAdditivity - max
    while (max < left) {
      val next = iterator.next
      if (next._2 > max) {
        result = next._1
        max = next._2
      }
      left -= next._2
    }
    result
  }
}

