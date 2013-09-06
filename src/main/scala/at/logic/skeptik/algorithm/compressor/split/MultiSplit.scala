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
extends AbstractSplitHeuristic {

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
      //the only other reasonable case is newDepth == 0, where branch is returned -> in other cases requirement depth > 0 is violated?
      if (newDepth > 0) SplitterTrunk(branch, newDepth) else branch.deepen(newDepth) 
    }
  }

  private case class SplitterNode (pos: Splitter, neg: Splitter)
  extends Splitter {
    def merge(variableList: List[E]) = variableList match {
      case t::q => R(pos.merge(q), neg.merge(q), t, true) //isn't the second (error) case called as soon q is empty?
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
          SplitterLeaf(R(proofLeft, proofRight, pivot, true))

        // Split case : the pivot matches the variable
        case (l, r) if pivot == variable =>
          Splitter(l.pos, r.neg)

        // Optimization case : if both premises have non-null depth we can remove some variables from the list
        case (left @ SplitterTrunk(_, depthLeft), right @ SplitterTrunk(_, depthRight)) => //this assignment with @ seems useless?
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
      {
      val x = node match {
      
        case Axiom(_) => Splitter(node, variableList) //redundant case with 3?
        case R(_,_,pivot,_) => Splitter(pivot, premises.head, premises.last, variableList)
        case _ => Splitter(node, variableList)
      }
//      println(x)
      x
      }
    proof foldDown {visit}
  }

  override def applyOnce(proof: Proof[SequentProofNode]) = {
    val (measures, measureSum) = computeMeasures(proof)
    var sum = measureSum
    val variableList = {
      def selectVariables(variableList: List[E], remaining: Int):List[E] = if (remaining < 1 || sum < 1) variableList else {
        val selected = chooseVariable(measures, sum)
        sum -= measures(selected)
        measures.remove(selected)
        selectVariables(selected::variableList, remaining - 1)
      }
      selectVariables(List(), numberOfVariables)
    }
    val compressedProof: Proof[SequentProofNode] = split(proof, variableList).merge(variableList)
//    if (compressedProof.size < proof.size) compressedProof else proof
//    compressedProof
    takeItOrLeaveIt(proof,compressedProof)
  }
  
  def takeItOrLeaveIt(proof:Proof[SequentProofNode],compressedProof:Proof[SequentProofNode]):Proof[SequentProofNode]
}

trait takeIt {
  def takeItOrLeaveIt(proof:Proof[SequentProofNode],compressedProof:Proof[SequentProofNode]):Proof[SequentProofNode] = compressedProof
}

trait leaveIt {
  def takeItOrLeaveIt(proof:Proof[SequentProofNode],compressedProof:Proof[SequentProofNode]):Proof[SequentProofNode] = if (compressedProof.size < proof.size) compressedProof else proof
}

class SimpleMultiSplit(numberOfVariables: Int)
extends MultiSplit(numberOfVariables) with AdditivityHeuristic with DeterministicChoice with takeIt{
  def apply(p: Proof[SequentProofNode]):Proof[SequentProofNode] = {
    applyOnce(p)
  }
}

class TimeoutMultiSplit(numberOfVariables: Int, val timeout: Int)
extends MultiSplit(numberOfVariables) with AdditivityHeuristic with DeterministicChoice with leaveIt with Timeout

class TakeItMultiSplit(numberOfVariables: Int, val timeout: Int)
extends MultiSplit(numberOfVariables) with AdditivityHeuristic with DeterministicChoice with takeIt with Timeout

class TakeItLeaveIrregularities(numberOfVariables: Int, val timeout: Int)
extends MultiSplit(numberOfVariables) with LeaveIrregularitiesHeuristic with DeterministicChoice with leaveIt with Timeout

class PRMultiSplit(numberOfVariables: Int, val timeout: Int)
extends MultiSplit(numberOfVariables) with PunishIrregularityHeuristic with DeterministicChoice with takeIt with Timeout

class SSMultiSplit(numberOfVariables: Int, val timeout: Int)
extends MultiSplit(numberOfVariables) with SequentSizeHeuristic with DeterministicChoice with takeIt with Timeout

class WDMultiSplit(numberOfVariables: Int, val timeout: Int)
extends MultiSplit(numberOfVariables) with WeightedDepthHeuristic with DeterministicChoice with takeIt with Timeout
