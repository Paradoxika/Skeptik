package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

abstract class AbstractSplit
extends (SequentProof => SequentProof) {
  
  protected def collectHeuristic(nodeCollection: ProofNodeCollection[SequentProof]) = {
    var heuristicSum = 0.toLong
    val heuristicMap = MMap[E,Long]()
    def visit(node: SequentProof) = node match {
      case CutIC(_,_,aux,_) =>
        val heuristicEval = ((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1
        heuristicSum += heuristicEval
        heuristicMap.update(aux, heuristicMap.getOrElse(aux,0.toLong) + heuristicEval)
      case _ =>
    }
    nodeCollection.foreach(visit)
    (heuristicMap, heuristicSum)
  }

  protected def chooseAVariable(heuristicMap: scala.collection.Map[E,Long], heuristicSum: Long):E
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

  protected def chooseAVariable(heuristicMap: scala.collection.Map[E,Long], heuristicSum: Long) = {
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
  protected def chooseAVariable(heuristicMap: scala.collection.Map[E,Long], heuristicSum: Long) = {
    val iterator = heuristicMap.toIterator
    var (result, max) = iterator.next
    var left = heuristicSum - max
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
abstract class Split (oneRun: Boolean)
extends AbstractSplit {
  private def split(nodeCollection: ProofNodeCollection[SequentProof], selectedVariable: E):SequentProof = {
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
          val newNode = if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node
                        else { println("yooups") ; CutIC(fixedLeftPos, fixedRightPos, _ == aux, true) }
          (newNode, newNode)

        case CutIC(left,right,aux,_) =>
          ( if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node else CutIC(fixedLeftPos, fixedRightPos, _ == aux, true),
            if ((left eq fixedLeftNeg) && (right eq fixedRightNeg)) node else CutIC(fixedLeftNeg, fixedRightNeg, _ == aux, true) )
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

/** Extended Split compression algorithm
 *
 * A arbitrary number of variables are selected and the proof is split in 2^n subproofs.
 */
abstract class MultiSplit (nbVariables: Int)
extends AbstractSplit {

  /** Binary tree to store partial proofs.
  *
  * Each level of the tree correspond to a selected variable.
  */
  private abstract sealed class Splitter {
    def pos:Splitter
    def neg:Splitter
    def depth:Int
    def merge(variableList: List[E]):SequentProof
    def deepen(amount: Int = 1):Splitter
  }

  private case class SplitterNode (deepPos: Splitter, deepNeg: Splitter, depth: Int = 0)
  extends Splitter {
    def pos = if (depth > 0) deepen(-1) else deepPos
    def neg = if (depth > 0) deepen(-1) else deepNeg
    def merge(variableList: List[E]) = variableList match {
      case t::q => CutIC(pos.merge(q), neg.merge(q), _ == t, true)
      case _ => throw new Exception("Variable list doen't correspond to Splitter structure")
    }
    def deepen(amount: Int = 1) = SplitterNode(deepPos, deepNeg, depth + amount)
    override def toString = "(" + pos.toString + " : " + neg.toString + " :" + depth + ")"
  }

  // A true leaf if depth == 0. A subtree with 2^depth identical leaves otherwise.
  private case class SplitterLeaf (proof: SequentProof, depth: Int = 0)
  extends Splitter {
    lazy val pos = if (depth > 0) deepen(-1) else throw new Exception("Traversing beyond leaves")
    def neg = pos
    def merge(variableList: List[E]) = proof
    def deepen(amount: Int = 1) = SplitterLeaf(proof, depth + amount)
    override def equals(other: Any):Boolean = other match {
      case SplitterLeaf(op, od) => (od == depth) && (op.conclusion == proof.conclusion)
      case _ => false
    }
    override def toString = "{" + proof.conclusion.toString + " :" + depth + "}"
  }

  private object Splitter {

    def apply(pos: Splitter, neg: Splitter):Splitter =
      if (pos == neg) pos.deepen() else SplitterNode(pos, neg)

    def apply(pivot: E, left: Splitter, right: Splitter, variableList: List[E]):Splitter = {
      lazy val variable = variableList.head // might throw an exception
      lazy val variableTail = variableList.tail
      val ret = (left, right) match {
        case (SplitterLeaf(proofLeft,0), SplitterLeaf(proofRight,0)) =>
          SplitterLeaf(CutIC(proofLeft, proofRight, _ == pivot, true))
        case (l, r) if pivot == variable =>
          Splitter(l.pos, r.neg)
        case (l, r) if (l.depth > 0) && (r.depth > 0) =>
          val depthMax = l.depth min r.depth
          def dive(depth: Int, variables: List[E]):(Int,List[E]) =
            if ((depth == depthMax) || (variables.head == pivot)) (depth, variables) else dive(depth + 1, variables.tail)
          val (depthDiff, variables) = dive(1, variableTail)
          Splitter(pivot, l.deepen(-depthDiff), r.deepen(-depthDiff), variables).deepen(depthDiff)
        case (l, r) =>
          Splitter(Splitter(pivot, l.pos, r.pos, variableTail), Splitter(pivot, l.neg, r.neg, variableTail))
      }
  //    println("split " + left + " and " + right + " on " + pivot + " with " + variableList + " gives " + ret)
      ret
    }

    def apply(axiom: SequentProof, variableList: List[E]):Splitter = new SplitterLeaf(axiom, variableList.length)
  }


  private def split(nodeCollection: ProofNodeCollection[SequentProof], variableList: List[E]) = {
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
