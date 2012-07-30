package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

abstract class AbstractSplit
extends (SequentProof => SequentProof) {
  
  protected def computeAdditivities(nodeCollection: ProofNodeCollection[SequentProof]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[E,Long]()
    def visit(node: SequentProof) = node match {
      case CutIC(_,_,aux,_) =>
        val nodeAdditivity = ((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1
        totalAdditivity += nodeAdditivity
        literalAdditivity.update(aux, literalAdditivity.getOrElse(aux,0.toLong) + nodeAdditivity)
      case _ =>
    }
    nodeCollection.foreach(visit)
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
abstract class Split (continueUntilCompression: Boolean)
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
    val (literalAdditivity, totalAdditivity) = computeAdditivities(nodeCollection)
    def repeat(sum: Long):SequentProof = {
      val selectedVariable = chooseAVariable(literalAdditivity, sum)
      val compressed = split(nodeCollection, selectedVariable)
      if (ProofNodeCollection(compressed).size < nodeCollection.size) compressed
      else {
        val newSum = sum - literalAdditivity(selectedVariable)
        if (!continueUntilCompression || newSum < 1) proof else {
          literalAdditivity.remove(selectedVariable)
          repeat(newSum)
        }
      }
    }
    repeat(totalAdditivity)
  }
}

/** Extended Split compression algorithm
 *
 * A arbitrary number of variables are selected and the proof is split in 2^n
 * subproofs.
 */
abstract class MultiSplit (nbVariables: Int)
extends AbstractSplit {

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
    def depth:Int
    def merge(variableList: List[E]):SequentProof
    def deepen(amount: Int = 1):Splitter
  }

  private case class SplitterNode (deepPos: Splitter, deepNeg: Splitter, depth: Int = 0)
  extends Splitter {
    def pos = if (depth > 0) deepen(-1) else deepPos
    def neg = if (depth > 0) deepen(-1) else deepNeg
    def merge(variableList: List[E]) =
      try {
        val tail = variableList.drop(depth + 1)
        CutIC(deepPos.merge(tail), deepNeg.merge(tail), _ == variableList(depth), true)
      }
      catch {
        case _: IndexOutOfBoundsException => throw new Exception("Variable list doen't correspond to Splitter structure")
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

        // Real leaf case : simple resolution
        case (SplitterLeaf(proofLeft,0), SplitterLeaf(proofRight,0)) =>
          SplitterLeaf(CutIC(proofLeft, proofRight, _ == pivot, true))

        // Split case : the pivot matches the variable
        case (l, r) if pivot == variable =>
          Splitter(l.pos, r.neg)

        // Optimization case : if both premises have non-nul depth we can remove some variables from the list
        case (l, r) if (l.depth > 0) && (r.depth > 0) =>
          val depthMax = l.depth min r.depth
          def dive(depth: Int, variables: List[E]):(Int,List[E]) =
            if ((depth == depthMax) || (variables.head == pivot)) (depth, variables) else dive(depth + 1, variables.tail)
          val (depthDiff, variables) = dive(1, variableTail)
          Splitter(pivot, l.deepen(-depthDiff), r.deepen(-depthDiff), variables).deepen(depthDiff)

        // Default recursive case
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
    val (literalAdditivity, totalAdditivity) = computeAdditivities(nodeCollection)
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
    val compressed = split(nodeCollection, variableList)
    if (ProofNodeCollection(compressed).size < nodeCollection.size) compressed else proof
  }
}
