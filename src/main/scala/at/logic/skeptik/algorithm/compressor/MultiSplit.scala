package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}


/** Extended Split compression algorithm
  *
  * A arbitrary number of variables are selected and the proof is split in 2^n
  * subproofs.
  */
abstract class MultiSplit (nbVariables: Int)
extends Split with AdditivityHeuristic {

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
  }

  private case class SplitterLeaf (node: SequentProofNode)
  extends Splitter {
    def pos = throw new Exception("Traversing beyond leaves")
    def neg = pos
    def merge(variableList: List[E]) = node
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
    def visit(node: SequentProofNode, premises: Seq[Splitter]) =
      node match {
        case Axiom(_) => Splitter(node, variableList)
        case CutIC(_,_,pivot,_) => Splitter(pivot, premises.head, premises.last, variableList)
        case _ => Splitter(node, variableList)
      }
    val result = proof.foldDown(visit)
    result.merge(variableList)
  }

  override def apply(proof: Proof[SequentProofNode]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    var sum = totalAdditivity
    val variableList = {
      def selectVariables(variableList: List[E], left: Int):List[E] = if (left < 1 || sum < 1) variableList else {
        val selected = chooseVariable(literalAdditivity, sum)
        sum -= literalAdditivity(selected)
        literalAdditivity.remove(selected)
        selectVariables(selected::variableList, left - 1)
      }
      selectVariables(List(), nbVariables)
    }
    split(proof, variableList)
  }
}
