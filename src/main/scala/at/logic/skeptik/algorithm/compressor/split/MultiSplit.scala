package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression._


/** Extended Split compression algorithm
  *
  * A arbitrary number of variables are selected and the proof is split in 2^n
  * subproofs.
  */
abstract class MultiSplit(numberOfVariables: Int)
extends AdditivityHeuristic {

  /** Binary tree to store partial proofs.
    *
    * Each level of the tree correspond to a selected variable.
    *
    * I've choose to not include those variables in the structure.  At first I
    * thought that including them would increase memory consumption. But later I
    * added a depth which would have been useless with a variable list. A better
    * reason is the symmetry between leaves' depth and nodes' depth. If depth is
    * replaced by a variable list, an empty list would be allowed for leaves but
    * not for nodes. It would introduce complication for the optimization case.
    * Another reason to not include variables in Splitter is what
    * I've understood about "referencial transparency": the variable list doesn't
    * have to be handled by Splitter but by the code that uses it.
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
  }

  private case class SplitterNode (pos: Splitter, neg: Splitter)
  extends Splitter {
    def merge(variableList: List[E]) = variableList match {
      case t::q => R(pos.merge(q), neg.merge(q), _ == t, true)
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
      lazy val variable = variableList.head // might throw an exception
      lazy val variableTail = variableList.tail
      val result = (left, right) match {

        // Real leaf case : simple resolution
        case (SplitterLeaf(proofLeft), SplitterLeaf(proofRight)) =>
          SplitterLeaf(R(proofLeft, proofRight, _ == pivot, true))

        // Split case : the pivot matches the variable
        case (l, r) if pivot == variable =>
          Splitter(l.pos, r.neg)

        // Optimization case : if both premises have non-null depth we can remove some variables from the list
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
      result
    }

    def apply(axiom: SequentProofNode, variableList: List[E]):Splitter = SplitterTrunk(SplitterLeaf(axiom), variableList.length)
  }


  private def split(proof: Proof[SequentProofNode], variableList: List[E]) = {
    def visit(node: SequentProofNode, premises: Seq[Splitter]) =
      node match {
        case Axiom(_) => Splitter(node, variableList)
        case R(_,_,pivot,_) => Splitter(pivot, premises.head, premises.last, variableList)
        case _ => Splitter(node, variableList)
      }
    proof foldDown {visit}
  }

  override def applyOnce(proof: Proof[SequentProofNode]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    var sum = totalAdditivity
    val variableList = {
      def selectVariables(variableList: List[E], remaining: Int):List[E] = if (remaining < 1 || sum < 1) variableList else {
        val selected = chooseVariable(literalAdditivity, sum)
        sum -= literalAdditivity(selected)
        literalAdditivity.remove(selected)
        selectVariables(selected::variableList, remaining - 1)
      }
      selectVariables(List(), numberOfVariables)
    }
    val compressedProof: Proof[SequentProofNode] = split(proof, variableList).merge(variableList)
    if (compressedProof.size < proof.size) compressedProof else proof
  }
}

class TimeoutMultiSplit(numberOfVariables: Int, val timeout: Int)
extends MultiSplit(numberOfVariables) with DeterministicChoice with Timeout