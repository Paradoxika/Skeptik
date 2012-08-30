package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

abstract class AbstractSplit
extends CompressorAlgorithm[SequentProofNode] {
  
  protected def computeAdditivities(proof: Proof[SequentProofNode]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[E,Long]()
    def visit(node: SequentProofNode) = node match {
      case CutIC(_,_,aux,_) =>
        val nodeAdditivity = ((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1
        totalAdditivity += nodeAdditivity
        literalAdditivity.update(aux, literalAdditivity.getOrElse(aux,0.toLong) + nodeAdditivity)
      case _ =>
    }
    proof.foreach(visit)
    (literalAdditivity, totalAdditivity)
  }

  protected def chooseAVariable(literalAdditivity: scala.collection.Map[E,Long], totalAdditivity: Long):E
}

trait RandomChoice
extends AbstractSplit {
  private val rand = new scala.util.Random()

  private def randomLong(max: Long):Long =
    if (max <= Int.MaxValue.toLong)
      rand.nextInt(max.toInt)
    else {
      var draw = rand.nextLong()
      if (draw < 0) draw = -draw
      if (draw < max) draw else ((draw - max).toDouble * max.toDouble / (Long.MaxValue - max).toDouble).toLong
    }

  protected def chooseAVariable(literalAdditivity: scala.collection.Map[E,Long], totalAdditivity: Long) = {
    val iterator = literalAdditivity.toIterator
    def searchPos(left: Long):E = {
      val next = iterator.next
      if (next._2 < left && iterator.hasNext) searchPos(left - next._2) else next._1
    }
    searchPos(randomLong(totalAdditivity) + 1)
  }
}

trait DeterministicChoice
extends AbstractSplit {
  protected def chooseAVariable(literalAdditivity: scala.collection.Map[E,Long], totalAdditivity: Long) = {
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


/** Cotton Split compression algorithm
 *
 * It's still 30% faster than MultiSplit(1).
 */
abstract class CottonSplit
extends AbstractSplit {
  protected def split(proof: Proof[SequentProofNode], selectedVariable: E):SequentProofNode = {
    def visit(node: SequentProofNode, fixedPremises: List[(SequentProofNode,SequentProofNode)]) = {
      lazy val (fixedLeftPos,  fixedLeftNeg)  = fixedPremises.head;
      lazy val (fixedRightPos, fixedRightNeg) = fixedPremises.last;
      node match {
        case Axiom(conclusion) => (node,node)
        case CutIC(_,_,aux,_) if aux == selectedVariable => (fixedLeftPos, fixedRightNeg)

        case CutIC(left,right,aux,_) if (fixedLeftPos eq fixedLeftNeg) && (fixedRightPos eq fixedRightNeg) =>
          // I think this case is redondant with the following one and then useless :
          // Neg and Pos being equals implies they're equals to node's premises.
          // Keep the println until it shows something.
          val newNode = if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node
                        else { println("yooups") ; CutIC(fixedLeftPos, fixedRightPos, _ == aux, true) }
          (newNode, newNode)

        case CutIC(left,right,aux,_) =>
          ( if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node else CutIC(fixedLeftPos, fixedRightPos, _ == aux, true),
            if ((left eq fixedLeftNeg) && (right eq fixedRightNeg)) node else CutIC(fixedLeftNeg, fixedRightNeg, _ == aux, true) )
      }
    }
    val (pos,neg) = proof.foldDown(visit)
    CutIC(pos, neg, _ == selectedVariable)
  }
}

abstract class Split
extends CottonSplit with RandomCompressionRepeatableAlgorithm[SequentProofNode] {
  def apply(proof: Proof[SequentProofNode]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    val selectedVariable = chooseAVariable(literalAdditivity, totalAdditivity)
    Proof(split(proof, selectedVariable))
  }
}

object Split
extends Split with RandomChoice

abstract class TerminatingSplit
extends CottonSplit with RepeatableWhileCompressingAlgorithm[SequentProofNode] {
  def apply(proof: Proof[SequentProofNode]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    def repeat(sum: Long):Proof[SequentProofNode] = {
      val selectedVariable = chooseAVariable(literalAdditivity, sum)
      val compressed = Proof(split(proof, selectedVariable))
      if (compressed.size < proof.size) compressed
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

object TerminatingSplitDeterministic
extends TerminatingSplit with DeterministicChoice

object TerminatingSplitRandom
extends TerminatingSplit with RandomChoice

/** Extended Split compression algorithm
  *
  * A arbitrary number of variables are selected and the proof is split in 2^n
  * subproofs.
  */
abstract class MultiSplit (nbVariables: Int)
extends AbstractSplit with RandomCompressionRepeatableAlgorithm[SequentProofNode] {

  /** Binary tree to store partial proofs.
    *
    * Each level of the tree correspond to a selected variable.
    *
    * I've choose to not include those variables in the structure.  At first I
    * thought that including them would increase memory consumption. But later I
    * added a depth which would have been useless with a variable list. A better
    * reason is the symetry between leaves' depth and nodes' depth. If depth is
    * replaced by a variable list, an empty list would be allowed for leaves but
    * not for nodes. It would introduce complication for the optimization case of
    * Split.apply. Another reason to not include variables in Splitter is what
    * I've understand about "referencial transparency". The variable list doesn't
    * have to be handled by Splitter but by the code which use it.
    *
    * An alternative implementation would be to add a
    *    case class Trunk(branch: Split, depth: Int)
    *
    */
  private abstract sealed class Splitter {
    def pos:Splitter
    def neg:Splitter
    def merge(variableList: List[E]):SequentProofNode

    def deepen(amount: Int = 1) = if (amount == 0) this else SplitterTrunk(this, amount)

    // to debug only
//    def debugDepth:Int
  }

  private case class SplitterTrunk (branch: Splitter, depth: Int = 1)
  extends Splitter {
    require(depth > 0)
    def pos = if (depth > 1) SplitterTrunk(branch, depth - 1) else branch
    def neg = pos
    def merge(variableList: List[E]) = branch.merge(variableList.drop(depth))

    override def deepen(amount: Int = 1) = {
      val newDepth = depth + amount
      if (newDepth > 0) SplitterTrunk(branch, newDepth) else branch.deepen(newDepth)
    }

//    def debugDepth = depth + branch.debugDepth
  }

  private case class SplitterNode (pos: Splitter, neg: Splitter)
  extends Splitter {
    def merge(variableList: List[E]) = variableList match {
      case t::q => CutIC(pos.merge(q), neg.merge(q), _ == t, true)
      case _ => throw new Exception("Variable list doen't correspond to Splitter structure")
    }

//    override def toString = "(" + pos.toString + " : " + neg.toString + ")"
//    def debugDepth = 1 + pos.debugDepth
  }

  private case class SplitterLeaf (node: SequentProofNode)
  extends Splitter {
    def pos = throw new Exception("Traversing beyond leaves")
    def neg = pos
    def merge(variableList: List[E]) = node

//    override def toString = "{" + node.conclusion.toString + "}"
//    def debugDepth = 0
  }

  private object Splitter {

    def apply(pos: Splitter, neg: Splitter):Splitter =
      if (pos == neg) pos.deepen() else SplitterNode(pos, neg)

    def apply(pivot: E, left: Splitter, right: Splitter, variableList: List[E]):Splitter = {
//      println("split " + left + " and " + right + " on " + pivot + " with " + variableList)
//      if (left.debugDepth != right.debugDepth) throw new Exception(left + " and " + right + " don't have same depth")
      lazy val variable = variableList.head // might throw an exception
      lazy val variableTail = variableList.tail
      val ret = (left, right) match {

        // Real leaf case : simple resolution
        case (SplitterLeaf(proofLeft), SplitterLeaf(proofRight)) =>
          SplitterLeaf(CutIC(proofLeft, proofRight, _ == pivot, true))

        // Split case : the pivot matches the variable
        case (l, r) if pivot == variable =>
          Splitter(l.pos, r.neg)

        // Optimization case : if both premises have non-nul depth we can remove some variables from the list
        case (left @ SplitterTrunk(_, depthLeft), right @ SplitterTrunk(_, depthRight)) =>
          val depthMax = depthLeft min depthRight
          val (depthDiff, variables) = {
            def dive(depth: Int, variables: List[E]):(Int,List[E]) =
              if ((depth == depthMax) || (variables.head == pivot)) (depth, variables) else dive(depth + 1, variables.tail)
            dive(1, variableTail)
          }
          Splitter(pivot, left.deepen(-depthDiff), right.deepen(-depthDiff), variables).deepen(depthDiff)

        // Default recursive case
        case (l, r) =>
          Splitter(Splitter(pivot, l.pos, r.pos, variableTail), Splitter(pivot, l.neg, r.neg, variableTail))
      }
//      println("split " + left + " and " + right + " on " + pivot + " with " + variableList + " gives " + ret)
//      if (ret.debugDepth != left.debugDepth) throw new Exception("Bug on split")
      ret
    }

    def apply(axiom: SequentProofNode, variableList: List[E]):Splitter = SplitterTrunk(SplitterLeaf(axiom), variableList.length)
  }


  private def split(proof: Proof[SequentProofNode], variableList: List[E]) = {
    def visit(node: SequentProofNode, premises: List[Splitter]) =
      node match {
        case Axiom(_) => Splitter(node, variableList)
        case CutIC(_,_,pivot,_) => Splitter(pivot, premises.head, premises.last, variableList)
      }
    val result = proof.foldDown(visit)
    result.merge(variableList)
  }

  override def apply(proof: Proof[SequentProofNode]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    var sum = totalAdditivity
    val variableList = {
      def selectVariables(variableList: List[E], left: Int):List[E] = if (left < 1 || sum < 1) variableList else {
        val selected = chooseAVariable(literalAdditivity, sum)
        sum -= literalAdditivity(selected)
        literalAdditivity.remove(selected)
        selectVariables(selected::variableList, left - 1)
      }
      selectVariables(List(), nbVariables)
    }
    Proof(split(proof, variableList))
  }
}
