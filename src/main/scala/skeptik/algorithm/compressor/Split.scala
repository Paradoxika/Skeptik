package skeptik.algorithm.compressor

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

abstract class Split
extends Function1[SequentProof,SequentProof] {
  
  def heuristic(node: SequentProof):Long = 
    ((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1

  def collectHeuristic(nodeCollection: ProofNodeCollection[SequentProof]) = {
    var heuristicSum = 0.toLong
    val heuristicMap = MMap[E,Long]()
    def visit(node: SequentProof) = node match {
      case CutIC(_,_,aux,_) =>
        val heuristicEval = heuristic(node)
        heuristicSum += heuristicEval
        heuristicMap.update(aux, heuristicMap.getOrElse(aux,0.toLong) + heuristicEval)
      case _ =>
    }
    nodeCollection.foreach(visit)
    (heuristicMap, heuristicSum)
  }

  def chooseAVariable(heuristicMap: scala.collection.Map[E,Long], heuristicSum: Long):E

  def split(nodeCollection: ProofNodeCollection[SequentProof], selectedVariable: E):SequentProof = {
    def fix(pivot: E, left: SequentProof, right: SequentProof) =
      (left.conclusion.suc contains pivot, right.conclusion.ant contains pivot) match {
        case (true, true)  => CutIC(left, right, _ == pivot)
        case (true, false) => right
        case (false,true)  => left
        case (false,false) => left
      }
    def visit(node: SequentProof, fixedPremises: List[(SequentProof,SequentProof)]) = {
      lazy val (fixedLeftPos,  fixedLeftNeg)  = fixedPremises.head;
      lazy val (fixedRightPos, fixedRightNeg) = fixedPremises.last;
      node match {
        case Axiom(conclusion) => (node,node)
        case CutIC(_,_,aux,_) if aux == selectedVariable => (fixedLeftPos, fixedRightNeg)
        case CutIC(_,_,aux,_) => (fix(aux, fixedLeftPos, fixedRightPos), fix(aux, fixedLeftNeg, fixedRightNeg))
      }
    }
    val (pos,neg) = nodeCollection.foldDown(visit)
    CutIC(pos, neg, _ == selectedVariable)
  }

  def apply(proof: SequentProof) = {
    val nodeCollection = ProofNodeCollection(proof)
    val (heuristicMap, heuristicSum) = collectHeuristic(nodeCollection)
    def repeat(sum: Long):SequentProof = {
      val selectedVariable = chooseAVariable(heuristicMap, sum)
      val compressed = split(nodeCollection, selectedVariable)
      if (ProofNodeCollection(compressed).size < nodeCollection.size) compressed
      else {
        val newSum = sum - heuristicMap(selectedVariable)
        if (newSum < 1) proof else {
          heuristicMap.remove(selectedVariable)
          repeat(newSum)
        }
      }
    }
    repeat(heuristicSum)
  }
}

trait RandomChoice
extends Split {
  private val rand = new scala.util.Random()

  def randomLong(max: Long):Long =
    if (max < Int.MaxValue.toLong) {
      if (max < 1) 0 else rand.nextInt(max.toInt)
    }
    else {
      def recursive():Long = {
        var ret = rand.nextLong()
        if (ret < 0) ret = -ret
        if (ret < max) ret else recursive()
      }
      recursive()
    }

  def chooseAVariable(heuristicMap: scala.collection.Map[E,Long], heuristicSum: Long) = {
    val iterator = heuristicMap.toIterator
    def searchPos(left: Long):E = {
      val next = iterator.next
      if (next._2 < left && iterator.hasNext) searchPos(left - next._2) else next._1
    }
    searchPos(randomLong(heuristicSum) + 1)
  }
}

trait DeterministicChoice
extends Split {
  def chooseAVariable(heuristicMap: scala.collection.Map[E,Long], heuristicSum: Long) =
    heuristicMap.max(Ordering.by[(E,Long),Long](_._2))._1
}

