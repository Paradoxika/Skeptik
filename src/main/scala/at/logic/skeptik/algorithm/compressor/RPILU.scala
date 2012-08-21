package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import collection.mutable.{HashMap => MMap, HashSet => MSet}
import collection.Map

abstract class AbstractRPILUAlgorithm
extends CompressorAlgorithm[SequentProof] {

  protected sealed abstract  class DeletedSide
  protected object LeftDS  extends DeletedSide
  protected object RightDS extends DeletedSide

  // Utility functions

  protected def childIsMarkedToDeleteParent(child: SequentProof, parent: SequentProof, edgesToDelete: Map[SequentProof,DeletedSide]) =
    (edgesToDelete contains child) &&
    (edgesToDelete(child) match {
      case LeftDS  => parent == child.premises(0)
      case RightDS => parent == child.premises(1)
    })

  protected def sideOf(parent: SequentProof, child: SequentProof) = child match {
    case CutIC(left, right, _,_) if parent == left  => LeftDS
    case CutIC(left, right, _,_) if parent == right => RightDS
    case _ => throw new Exception("Unable to find parent in child")
  }

  protected def isUnit(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof]) =
    (fakeSize(proof.conclusion.ant) + fakeSize(proof.conclusion.suc) == 1) &&
    (fakeSize(nodeCollection.childrenOf(proof)) > 1)

  protected def deleteFromChildren(oldProof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) =
    nodeCollection.childrenOf(oldProof).foreach { child =>
      // Deleting both premises of a node being too complicated, regularization takes precedence over unit lowering.
      if (!(edgesToDelete contains child)) edgesToDelete.update(child, sideOf(oldProof, child))
    }

  // Main functions

  protected def fixProofs(edgesToDelete: Map[SequentProof,DeletedSide])
               (p: SequentProof, fixedPremises: List[SequentProof]) = {
    lazy val fixedLeft  = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => p

      // If we've got a proof of false, we progate it down the proof
      case CutIC(_,_,_,_) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) => fixedLeft
      case CutIC(_,_,_,_) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) => fixedRight

      case CutIC(left,right,_,_) if edgesToDelete contains p => edgesToDelete(p) match {
        case LeftDS  => fixedRight
        case RightDS => fixedLeft
      }

      // If premises haven't been changed, we keep the proof as is (memory optimisation)
      case CutIC(left,right,_,_) if (left eq fixedLeft) && (right eq fixedRight) => p

      case CutIC(left,right,pivot,_) => CutIC(fixedLeft, fixedRight, _ == pivot, true)
    }
  }
}

abstract class AbstractRPIAlgorithm
extends AbstractRPILUAlgorithm {

  protected def safeLiteralsFromChild (childWithSafeLiterals: (SequentProof, IClause),
                                       parent: SequentProof, edgesToDelete: Map[SequentProof,DeletedSide]) =
    childWithSafeLiterals match {
      case (node, safeLiterals) if edgesToDelete contains node => safeLiterals
      case (CutIC(left,_,_,auxR),  safeLiterals) if left  == parent => safeLiterals + auxR
      case (CutIC(_,right,auxL,_), safeLiterals) if right == parent => auxL +: safeLiterals
      case _ => throw new Exception("Unknown or impossible inference rule")
    }

  protected def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, IClause)],
                          edgesToDelete: Map[SequentProof,DeletedSide]
                          ) : IClause

}

trait CollectEdgesUsingSafeLiterals
extends AbstractRPIAlgorithm {
  
  protected def collectEdgesToDelete(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      p match {
        case CutIC(_,_,auxL,_) if safeLiterals.suc contains auxL => edgesToDelete.update(p, RightDS)
        case CutIC(_,_,_,auxR) if safeLiterals.ant contains auxR => edgesToDelete.update(p, LeftDS)
        case _ =>
      }
      (p, safeLiterals)
    }
    nodeCollection.bottomUp(visit)
    edgesToDelete
  }
}

trait UnitsCollectingBeforeFixing
extends AbstractRPILUAlgorithm {
  protected def mapFixedProofs(proofsToMap: Set[SequentProof],
                     edgesToDelete: Map[SequentProof,DeletedSide],
                     nodeCollection: ProofNodeCollection[SequentProof]) = {
    val fixMap = MMap[SequentProof,SequentProof]()
    def visit (p: SequentProof, fixedPremises: List[SequentProof]) = {
      val result = fixProofs(edgesToDelete)(p, fixedPremises)
//      if (proofsToMap contains p) { fixMap.update(p, result) ; println(p.conclusion + " => " + result.conclusion) }
      if (proofsToMap contains p) fixMap.update(p, result)
      result
    }
    nodeCollection.foldDown(visit)
    fixMap
  }
}

trait Intersection
extends AbstractRPIAlgorithm {
  protected def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, IClause)],
                          edgesToDelete: Map[SequentProof,DeletedSide]
                          ) : IClause = {
    childrensSafeLiterals.filter { x => !childIsMarkedToDeleteParent(x._1, proof, edgesToDelete)} match {
      case Nil  => proof.conclusion.toSetSequent
      case h::t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) => acc intersect safeLiteralsFromChild(v, proof, edgesToDelete) }
    }
  }
}

