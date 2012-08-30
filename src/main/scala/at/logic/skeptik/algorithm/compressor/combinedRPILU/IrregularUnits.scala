package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import collection.Map

abstract class IrregularUnits
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection {

  protected def lowerInsteadOfRegularize(node: SequentProofNode, currentChildrenNumber: Int):Boolean

  private def collect(proof: Proof[SequentProofNode]) = {
    val edgesToDelete = MMap[SequentProofNode,DeletedSide]()
    val units = collection.mutable.Queue[SequentProofNode]()

    def isUnitAndSomething(something: (SequentProofNode, Int) => Boolean)
                          (p: SequentProofNode) =
      (fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc) == 1) && {
        val currentChildrenNumber = proof.childrenOf(p).foldLeft(0) { (acc,child) =>
          if (childIsMarkedToDeleteParent(child, p, edgesToDelete)) acc else (acc + 1)
        }
        (currentChildrenNumber > 1) && (something(p, currentChildrenNumber))
      }
    val isUnitToLower = isUnitAndSomething(lowerInsteadOfRegularize _) _
    val isTrueUnit = isUnitAndSomething { (_,_) => true } _


    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      def regularize(position: DeletedSide) = 
        if (isUnitToLower(p)) lower() else {
          edgesToDelete.update(p, position)
          (p, safeLiterals)
        }
      def lower() = {
        units.enqueue(p)
        deleteFromChildren(p, proof, edgesToDelete)
        if (fakeSize(p.conclusion.ant) == 1)
          (p, new IClause(Set(p.conclusion.ant(0)), Set[E]()))
        else
          (p, new IClause(Set[E](), Set(p.conclusion.suc(0))))
      }
      p match {
        case CutIC(_,_,_,auxR) if safeLiterals.ant contains auxR => regularize(LeftDS)
        case CutIC(_,_,auxL,_) if safeLiterals.suc contains auxL => regularize(RightDS)
        case p => if (isTrueUnit(p)) lower() else (p, safeLiterals)
      }
    }

    proof.bottomUp(visit)
    (units,edgesToDelete)
  }

  def apply(proof: Proof[SequentProofNode]) = {
    val (units,edgesToDelete) = collect(proof)
    if (edgesToDelete.isEmpty) proof else Proof({
      val fixMap = mapFixedProofNodes(units.toSet + proof.root, edgesToDelete, proof)
      units.map(fixMap).foldLeft(fixMap(proof.root)) { (left,right) =>
        // Right is a unit. No choice for a pivot.
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    })
  }
}

trait AlwaysLowerIrregularUnits extends IrregularUnits {
  protected def lowerInsteadOfRegularize(node: SequentProofNode, currentChildrenNumber: Int):Boolean = true
}

trait AlwaysRegularizeIrregularUnits extends IrregularUnits {
  protected def lowerInsteadOfRegularize(node: SequentProofNode, currentChildrenNumber: Int):Boolean = false
}

object IdempotentIrregularUnitsLower
extends IrregularUnits with AlwaysLowerIrregularUnits with IdempotentAlgorithm[SequentProofNode]

object IdempotentIrregularUnitsRegularize
extends IrregularUnits with AlwaysRegularizeIrregularUnits with IdempotentAlgorithm[SequentProofNode]
