package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.Map

abstract class AbstractRPILUAlgorithm
extends CompressorAlgorithm[SequentProof] {

  protected sealed abstract  class DeletedSide
  protected object LeftDS  extends DeletedSide
  protected object RightDS extends DeletedSide
  protected object BothDS  extends DeletedSide

  class EdgesToDelete {
    // The progation of deletion when both premises are deleted is done during fixing.

    val edges = MMap[SequentProof,DeletedSide]()

    def markEdge(node: SequentProof, premiseSide: DeletedSide) =
      edges.update(node, if (edges contains node) BothDS else premiseSide)

    def markOutgoing(node: SequentProof, premises: SequentProof*) =
      premises.foreach { (premise) =>
        markEdge(node, sideOf(premise, node))
      }

    def markIncoming(node: SequentProof, children: SequentProof*) =
      children.foreach { (child) =>
        markEdge(node, sideOf(node, child))
      }

    def deleteNode(node: SequentProof) =
      edges.update(node, BothDS)

    def deletedSide(node: SequentProof) = edges.get(node)

    def isEmpty = edges.isEmpty

    private def markIs(node: SequentProof, side: DeletedSide) =
      // TODO : remove it if it's not used often enough
      (edges contains node) && (edges(node) == side)

    def isMarked(node: SequentProof, premise: SequentProof):Boolean =  
      // may be optimzed
      ((edges contains node) && (edges(node) == BothDS || edges(node) == sideOf(premise, node))) || nodeIsMarked(premise)

    def nodeIsMarked(node: SequentProof):Boolean =
      // may be optimized (edgesToDelete contains node is checked 3 times)
      node match {
        case _ if markIs(node, BothDS) => true
        case CutIC(left,right,_,_) if (isMarked(node, left) && isMarked(node,right)) =>
          edges(node) = BothDS
          true
        case _ => false
      }
  }

  // Utility functions

  protected def sideOf(parent: SequentProof, child: SequentProof) = child match {
    case CutIC(left, right, _,_) if parent == left  => LeftDS
    case CutIC(left, right, _,_) if parent == right => RightDS
    case _ => throw new Exception("Unable to find parent in child")
  }

  protected def isUnit(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof]) =
    (fakeSize(proof.conclusion.ant) + fakeSize(proof.conclusion.suc) == 1) &&
    (fakeSize(nodeCollection.childrenOf(proof)) > 1)


  // Main functions

  protected def fixProofs(edgesToDelete: EdgesToDelete)
               (p: SequentProof, fixedPremises: List[SequentProof]) = {
    lazy val fixedLeft  = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => p

      // If we've got a proof of false, we progate it down the proof
      case CutIC(_,_,_,_) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) => fixedLeft
      case CutIC(_,_,_,_) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) => fixedRight

      // Delete nodes and edges
      case _ if edgesToDelete.nodeIsMarked(p) => p
      case CutIC(left,right,_,_) if edgesToDelete.isMarked(p,left)  => right
      case CutIC(left,right,_,_) if edgesToDelete.isMarked(p,right) => left

      // If premises haven't been changed, we keep the proof as is (memory optimisation)
      case CutIC(left,right,_,_) if (left eq fixedLeft) && (right eq fixedRight) => p

      // Main case (rebuild a resolution)
      case CutIC(left,right,pivot,_) => CutIC(fixedLeft, fixedRight, _ == pivot, true)
    }
  }
}

abstract class AbstractRPIAlgorithm
extends AbstractRPILUAlgorithm {

  protected def safeLiteralsFromChild (childWithSafeLiterals: (SequentProof, IClause),
                                       parent: SequentProof, edgesToDelete: EdgesToDelete) =
    childWithSafeLiterals match {
      case (node, safeLiterals) if edgesToDelete.isMarked(node,parent) => safeLiterals
      case (CutIC(left,_,_,auxR),  safeLiterals) if left  == parent => safeLiterals + auxR
      case (CutIC(_,right,auxL,_), safeLiterals) if right == parent => auxL +: safeLiterals
      case _ => throw new Exception("Unknown or impossible inference rule")
    }

  protected def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, IClause)],
                          edgesToDelete: EdgesToDelete
                          ) : IClause

}

trait CollectEdgesUsingSafeLiterals
extends AbstractRPIAlgorithm {
  
  protected def collectEdgesToDelete(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = new EdgesToDelete()
    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      p match {
        case CutIC(_,_,auxL,_) if safeLiterals.suc contains auxL => edgesToDelete.markEdge(p, RightDS)
        case CutIC(_,_,_,auxR) if safeLiterals.ant contains auxR => edgesToDelete.markEdge(p, LeftDS)
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
                     edgesToDelete: EdgesToDelete,
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
                          edgesToDelete: EdgesToDelete
                          ) : IClause = {
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof)} match {
      case Nil  => IClause(proof.conclusion)
      case h::t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) => acc intersect safeLiteralsFromChild(v, proof, edgesToDelete) }
    }
  }
}
