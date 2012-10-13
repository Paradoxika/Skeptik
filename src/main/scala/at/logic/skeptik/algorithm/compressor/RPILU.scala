package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import collection.mutable.{HashMap => MMap, HashSet => MSet}
import collection.Map

abstract class AbstractRPILUAlgorithm
extends CompressorAlgorithm[SequentProofNode] {

  protected sealed abstract  class DeletedSide
  protected object NoDS    extends DeletedSide
  protected object LeftDS  extends DeletedSide
  protected object RightDS extends DeletedSide

  class EdgesToDelete {

    val edges = MMap[SequentProofNode,(DeletedSide,Boolean)]()

    private def otherSide(side: DeletedSide) =
      side match {
        case LeftDS => RightDS
        case RightDS => LeftDS
        case _ => NoDS
      }

    def markEdge(node: SequentProofNode, premiseSide: DeletedSide) = {
//      if ((edges contains node) && (edges(node)._1 == otherSide(premiseSide))) println("Case A")
      val deleteNode = (edges contains node) &&
                       { val old = edges(node) ; old._2 || old._1 == otherSide(premiseSide) }
      edges(node) = (premiseSide, deleteNode)
    }

    def deleteNode(node: SequentProofNode) =
      edges(node) = (edges.getOrElse(node,(NoDS,true))._1, true)

    def deletedSide(node: SequentProofNode) =
      edges.get(node) match {
        case Some((NoDS,_)) => None
        case Some((s,_))    => Some(s)
        case None           => None
      }

    def isEmpty = edges.isEmpty

    def isMarked(node: SequentProofNode, premise: SequentProofNode):Boolean =
      ((edges contains node) && (edges(node)._1 == sideOf(premise, node))) || nodeIsMarked(premise)

    def nodeIsMarked(node: SequentProofNode):Boolean =
      // may be optimized (edgesToDelete contains node is checked 3 times)
      node match {
        case _ if ((edges contains node) && edges(node)._2) => true
        case CutIC(left,right,_,_) if (isMarked(node, left) && isMarked(node,right)) =>
//          println("Case B")
          deleteNode(node)
          true
        case _ => false
      }
  }

  // Utility functions

  protected def sideOf(parent: SequentProofNode, child: SequentProofNode) = child match {
    case CutIC(left, right, _,_) if parent == left  => LeftDS
    case CutIC(left, right, _,_) if parent == right => RightDS
    case _ => throw new Exception("Unable to find parent in child")
  }

  protected def isUnit(proof: SequentProofNode, nodeCollection: Proof[SequentProofNode]) =
    (fakeSize(proof.conclusion.ant) + fakeSize(proof.conclusion.suc) == 1) &&
    (fakeSize(nodeCollection.childrenOf(proof)) > 1)


  // Main functions

  protected def fixProofNodes(edgesToDelete: EdgesToDelete)
               (p: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
    lazy val fixedLeft  = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => p

      // If we've got a proof of false, we progate it down the proof
      case CutIC(_,_,_,_) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) =>
        fixedLeft
      case CutIC(_,_,_,_) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) =>
        fixedRight

      // Delete nodes and edges
      case CutIC(left,right,_,_) if edgesToDelete.isMarked(p,left) =>
        fixedRight
      case CutIC(left,right,_,_) if edgesToDelete.isMarked(p,right) =>
        fixedLeft

      // If premises haven't been changed, we keep the proof as is (memory optimisation)
      case CutIC(left,right,_,_) if (left eq fixedLeft) && (right eq fixedRight) => p

      // Main case (rebuild a resolution)
      case CutIC(left,right,pivot,_) => CutIC(fixedLeft, fixedRight, _ == pivot, true)
    }
  }
}

abstract class AbstractRPIAlgorithm
extends AbstractRPILUAlgorithm {

  protected def safeLiteralsFromChild (childWithSafeLiterals: (SequentProofNode, IClause),
                                       parent: SequentProofNode, edgesToDelete: EdgesToDelete) =
    childWithSafeLiterals match {
      case (child @ CutIC(left,right,_,auxR), safeLiterals) if left  == parent => 
        if (edgesToDelete.isMarked(child,right)) safeLiterals else (safeLiterals + auxR)
      case (child @ CutIC(left,right,auxL,_), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child,left))  safeLiterals else (auxL +: safeLiterals)
      case _ => throw new Exception("Unknown or impossible inference rule")
    }

  protected def computeSafeLiterals(proof: SequentProofNode,
                          childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
                          edgesToDelete: EdgesToDelete
                          ) : IClause

}

trait CollectEdgesUsingSafeLiterals
extends AbstractRPIAlgorithm {
  
  protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
    val edgesToDelete = new EdgesToDelete()
    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
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
  protected def mapFixedProofNodes(proofsToMap: Set[SequentProofNode],
                     edgesToDelete: EdgesToDelete,
                     nodeCollection: Proof[SequentProofNode]) = {
    val fixMap = MMap[SequentProofNode,SequentProofNode]()
    def visit (p: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
      val result = fixProofNodes(edgesToDelete)(p, fixedPremises)
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
  protected def computeSafeLiterals(proof: SequentProofNode,
                          childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
                          edgesToDelete: EdgesToDelete
                          ) : IClause = {
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof)} match {
      case Nil  => proof.conclusion.toSetSequent
      case h::t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) => acc intersect safeLiteralsFromChild(v, proof, edgesToDelete) }
    }
  }
}
