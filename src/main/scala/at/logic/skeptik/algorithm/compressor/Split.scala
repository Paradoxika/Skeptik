package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

abstract class AbstractSplit
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
}

trait RandomChoice
extends AbstractSplit {
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
extends AbstractSplit {
  def chooseAVariable(heuristicMap: scala.collection.Map[E,Long], heuristicSum: Long) =
    heuristicMap.max(Ordering.by[(E,Long),Long](_._2))._1
}


/** Cotton Split compression algorithm
 *
 * It's still 30% faster than MultiSplit(1).
 */
abstract class Split (oneRun: Boolean)
extends AbstractSplit {
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

        case CutIC(left,right,aux,_) if (fixedLeftPos eq fixedLeftNeg) && (fixedRightPos eq fixedRightNeg) =>
          // I think this case is redondant with the following one and then useless :
          // Neg and Pos being equals implies they're equals to node's premises.
          // Keep the println until it shows something.
          val newNode = if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node else {println("yooups") ; fix(aux, fixedLeftPos, fixedRightPos)}
          (newNode, newNode)

        case CutIC(left,right,aux,_) =>
          ( if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node else fix(aux, fixedLeftPos, fixedRightPos),
            if ((left eq fixedLeftNeg) && (right eq fixedRightNeg)) node else fix(aux, fixedLeftNeg, fixedRightNeg) )
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
        if (oneRun || newSum < 1) proof else {
          heuristicMap.remove(selectedVariable)
          repeat(newSum)
        }
      }
    }
    repeat(heuristicSum)
  }
}


/** Binary tree to store partial proofs.
 *
 * Each level of the tree correspond to a selected variable.
 */
abstract sealed class Splitter {
  def pos:Splitter
  def neg:Splitter
  def merge(variableList: List[E]):SequentProof
}

// TODO: add a depth
case class SplitterNode (pos: Splitter, neg: Splitter)
extends Splitter {
  def merge(variableList: List[E]) = variableList match {
    case t::q => Splitter.fix(t, pos.merge(q), neg.merge(q))
    case _ => throw new Exception("Variable list doen't correspond to Splitter structure")
  }
  override def toString = "(" + pos.toString + " : " + neg.toString + ")"
}

// A true leaf if depth == 0. A subtree with 2^depth identical leaves otherwise.
case class SplitterLeaf (proof: SequentProof, depth: Int = 0)
extends Splitter {
  lazy val pos = if (depth > 0) SplitterLeaf(proof, depth - 1) else throw new Exception("Traversing beyond leaves")
  def neg = pos
  def merge(variableList: List[E]) = proof
  override def toString = proof.conclusion.toString
}

object Splitter {

  // TODO: Move ? Share ?
  def fix(pivot: E, left: SequentProof, right: SequentProof) =
    (left.conclusion.suc contains pivot, right.conclusion.ant contains pivot) match {
      case (true, true)  => CutIC(left, right, _ == pivot)
      case (true, false) => right
      case (false,true)  => left
      case (false,false) => left
    }

  def apply(pos: Splitter, neg: Splitter):Splitter = (pos,neg) match {
    case (SplitterLeaf(proofPos, depthPos), SplitterLeaf(proofNeg, depthNeg)) if (depthPos == depthNeg) && (proofPos.conclusion == proofNeg.conclusion) =>
      SplitterLeaf(proofPos, depthPos + 1)
    case _ => SplitterNode(pos, neg)
  }

  def apply(pivot: E, left: Splitter, right: Splitter, variableList: List[E]):Splitter = {
    lazy val variable = variableList.head // might throw an exception
    lazy val variableTail = variableList.tail
    val ret = (left, right) match {
      case (SplitterLeaf(proofLeft,0), SplitterLeaf(proofRight,0)) =>
        SplitterLeaf(fix(pivot, proofLeft, proofRight))
      case (l, r) if pivot == variable =>
        Splitter(l.pos, r.neg)
      case (l, r) =>
        Splitter(Splitter(pivot, l.pos, r.pos, variableTail), Splitter(pivot, l.neg, r.neg, variableTail))
    }
    ret
  }

  def apply(axiom: SequentProof, variableList: List[E]):Splitter = new SplitterLeaf(axiom, variableList.length)

}

/** Extended Split compression algorithm
 *
 * A arbitrary number of variables are selected and the proof is split in 2^n subproofs.
 */
abstract class MultiSplit (nbVariables: Int)
extends AbstractSplit {

  def split(nodeCollection: ProofNodeCollection[SequentProof], variableList: List[E]) = {
    def visit(node: SequentProof, premises: List[Splitter]) =
      node match {
        case Axiom(_) => Splitter(node, variableList)
        case CutIC(_,_,pivot,_) => Splitter(pivot, premises.head, premises.last, variableList)
      }
    val result = nodeCollection.foldDown(visit)
    result.merge(variableList)
  }

  override def apply(proof: SequentProof) = {
    val nodeCollection = ProofNodeCollection(proof)
    val (heuristicMap, heuristicSum) = collectHeuristic(nodeCollection)
    var sum = heuristicSum
    def selectVariables(variableList: List[E], left: Int):List[E] = if (left < 1 || sum < 1) variableList else {
      val selected = chooseAVariable(heuristicMap, sum)
      sum -= heuristicMap(selected)
      heuristicMap.remove(selected)
      selectVariables(selected::variableList, left - 1)
    }
    val variableList = selectVariables(List(), nbVariables)
    val compressed = split(nodeCollection, variableList)
    if (ProofNodeCollection(compressed).size < nodeCollection.size) compressed else proof
  }
} 

