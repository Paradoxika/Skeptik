package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

abstract class IrregularUnits
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection {

  protected def lowerInsteadOfRegularize(proof: SequentProof, currentChildrenNumber: Int):Boolean

  private def collect(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val units = scala.collection.mutable.Queue[SequentProof]()

    def isUnitAndSomething(something: (SequentProof, Int) => Boolean)
                          (p: SequentProof) =
      (fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc) == 1) && {
        val currentChildrenNumber = nodeCollection.childrenOf(p).foldLeft(0) { (acc,child) =>
          if (childIsMarkedToDeleteParent(child, p, edgesToDelete)) acc else (acc + 1)
        }
        (currentChildrenNumber > 1) && (something(p, currentChildrenNumber))
      }
    val isUnitToLower = isUnitAndSomething(lowerInsteadOfRegularize _) _
    val isTrueUnit = isUnitAndSomething { (_,_) => true } _


    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      def safeLiteralsFromChild(v:(SequentProof, IClause)) = v match {
        case (p, safeLiterals) if edgesToDelete contains p => safeLiterals
        case (CutIC(left,_,_,auxR),  safeLiterals) if left  == p => safeLiterals + auxR
        case (CutIC(_,right,auxL,_), safeLiterals) if right == p => auxL +: safeLiterals
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
      def regularize(position: DeletedSide) = 
        if (isUnitToLower(p)) lower() else {
          edgesToDelete.update(p, position)
          (p, safeLiterals)
        }
      def lower() = {
        units.enqueue(p)
        deleteFromChildren(p, nodeCollection, edgesToDelete)
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

    nodeCollection.bottomUp(visit)
    (units,edgesToDelete)
  }

  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val (units,edgesToDelete) = collect(nodeCollection)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, nodeCollection)
      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
        // Right is a unit. No choice for a pivot.
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }
}

trait AlwaysLowerIrregularUnits extends IrregularUnits {
  protected def lowerInsteadOfRegularize(proof: SequentProof, currentChildrenNumber: Int):Boolean = true
}

trait AlwaysRegularizeIrregularUnits extends IrregularUnits {
  protected def lowerInsteadOfRegularize(proof: SequentProof, currentChildrenNumber: Int):Boolean = {
//    println("Irregular unit " + proof.conclusion + " with " + currentChildrenNumber + " children")
    false
  }
}
