package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

// There is a lot of code duplication and other ugly things.
// Class Split should be deleted and replaced by MultiSplit.
// Then this file'll be cleaned.

abstract class Split (oneRun: Boolean)
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

        case CutIC(left,right,aux,_) if (fixedLeftPos eq fixedLeftNeg) && (fixedRightPos eq fixedRightNeg) =>
          // I think this case is redondant with the following one and then useless :
          // Neg and Pos being equals implies they're equals to node's premises.
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


// Binary tree to store partial proofs
abstract sealed class Splitter {
  def merge(variableList: List[E]):SequentProof
}

case class SplitterNode (left: Splitter, right: Splitter)
extends Splitter {
  def merge(variableList: List[E]) = variableList match {
//    case t::q => println("merging on " + t) ; Splitter.fix(t, left.merge(q), right.merge(q))
    case t::q => Splitter.fix(t, left.merge(q), right.merge(q))
    case _ => throw new Exception("Variable list doen't correspond to Splitter structure")
  }
  override def toString = "(" + left.toString + " : " + right.toString + ")"
}

// TODO: Add a depth to minimize nodes duplications.
case class SplitterLeaf (proof: SequentProof)
extends Splitter {
//  def merge(variableList: List[E]) = { println("merging " + proof.conclusion) ; proof }
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

  def apply(pivot: E, left: Splitter, right: Splitter, variableList: List[E]):Splitter = {
    lazy val variable = variableList.head // might throw an exception
    lazy val variableTail = variableList.tail
    val ret = (left, right) match {
      case (l:SplitterNode, r:SplitterNode) if pivot == variable =>
        new SplitterNode(l.left, r.right)
      case (l:SplitterNode, r:SplitterNode) =>
        new SplitterNode(Splitter(pivot, l.left, r.left, variableTail), Splitter(pivot, l.right, r.right, variableTail))
      case (l:SplitterLeaf, r:SplitterLeaf) =>
        new SplitterLeaf(fix(pivot, l.proof, r.proof))
      case _ => throw new Exception("Splitters with different structures")
    }
//    println("Splitting " + left + " and " + right + " on " + pivot + " result in " + ret)
    ret
  }

  def apply(axiom: SequentProof, variableList: List[E]):Splitter = {
    def repeat(splitter: Splitter, list: List[E]):Splitter = list match {
      case Nil => splitter
      case _::q => repeat(new SplitterNode(splitter, splitter), q)
    }
    repeat(new SplitterLeaf(axiom), variableList)
  }

}



abstract class MultiSplit (nbVariables: Int, oneRun: Boolean)
extends Split(oneRun) {

  def split(nodeCollection: ProofNodeCollection[SequentProof], variableList: List[E]) = {
    def visit(node: SequentProof, premises: List[Splitter]) =
      node match {
        case Axiom(_) => Splitter(node, variableList)
        case CutIC(_,_,pivot,_) => Splitter(pivot, premises.head, premises.last, variableList)
      }
    val result = nodeCollection.foldDown(visit)
//    println("V " + variableList)
//    println("R " + result)
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
    def repeat():SequentProof = {
//      println("Choose " + heuristicMap.keys + " sum " + sum)
      val variableList = selectVariables(List(), nbVariables)
      val compressed = split(nodeCollection, variableList)
      if (ProofNodeCollection(compressed).size < nodeCollection.size) compressed
      else if (oneRun || sum < 1) proof else repeat()
    }
    repeat()
  }
} 

abstract class MultiSplitWithDAG (nbVariables: Int)
extends MultiSplit (nbVariables, true) {
  override def split(nodeCollection: ProofNodeCollection[SequentProof], variableList: List[E]) = DAGification(super.split(nodeCollection,variableList))
}

