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
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {



  class EdgesToDelete {
    
    protected sealed abstract  class DeletedSide
    protected case object NoDS    extends DeletedSide
    protected case object LeftDS  extends DeletedSide
    protected case object RightDS extends DeletedSide
    protected case object BothDS  extends DeletedSide

    val edges = MMap[SequentProofNode,(DeletedSide,Boolean)]()

    private def otherSide(side: DeletedSide) = side match {
      case LeftDS => RightDS
      case RightDS => LeftDS
      case _ => NoDS
    }

    def markEdge(node: SequentProofNode, premiseSide: DeletedSide) = {
      edges(node) = edges.get(node) match {
        case None => (premiseSide, false)
        case Some((BothDS,_)) => (BothDS, true)
        case Some((side,_)) if side == otherSide(premiseSide) => (BothDS, true)
        case Some((_,del)) => (premiseSide, del)
      }
    }

    def markEdge(child: SequentProofNode, premise: SequentProofNode):Unit =
      markEdge(child, sideOf(premise, child))

    def markBothEdges(node: SequentProofNode) = { edges(node) = (BothDS, true) }
    
    def markLeftEdge(node: SequentProofNode) = markEdge(node, LeftDS)
    
    def markRightEdge(node: SequentProofNode) = markEdge(node, RightDS)
    
    def deleteNode(node: SequentProofNode) =
      edges(node) = (edges.getOrElse(node,(NoDS,true))._1, true)

    def deletedSide(node: SequentProofNode) =
      edges.get(node) match {
        case Some((NoDS,_)) => None
        case Some((s,_))    => Some(s)
        case None           => None
      }

    def isEmpty = edges.isEmpty

    def isMarked(node: SequentProofNode, premise: SequentProofNode):Boolean = {
      (edges.get(node) match {
        case None => false
        case Some((BothDS,_)) => true
        case Some((NoDS,true)) => false
        case Some((side,_)) => side == sideOf(premise, node)
      }) || nodeIsMarked(premise)
    }

    def nodeIsMarked(node: SequentProofNode):Boolean = {
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
    
    protected def sideOf(parent: SequentProofNode, child: SequentProofNode) = child match {
      case CutIC(left, right, _,_) => if (parent == left) LeftDS
                                      else if (parent == right) RightDS
                                      else throw new Exception("Unable to find parent in child")
      case _ => throw new Exception("This function should never be called with child not being a CutIC")
    }

  }

  // Utility functions

  protected def isUnit(proof: SequentProofNode, nodeCollection: Proof[SequentProofNode]) =
    (proof.conclusion.ant.length + proof.conclusion.suc.length == 1) &&
    (nodeCollection.childrenOf(proof).length > 1)


  // Main functions

  protected def fixProofNodes(edgesToDelete: EdgesToDelete)
               (p: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
    lazy val fixedLeft  = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => p

      // If we've got a proof of false, we propagate it down the proof
      case CutIC(_,_,_,_) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) =>
        fixedLeft
      case CutIC(_,_,_,_) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) =>
        fixedRight

      // Delete nodes and edges
      case CutIC(left,right,_,_) if edgesToDelete.isMarked(p,left) =>
        fixedRight
      case CutIC(left,right,_,_) if edgesToDelete.isMarked(p,right) =>
        fixedLeft

      // If premises haven't been changed, we keep the proof as is (memory optimization)
      case CutIC(left,right,_,_) if (left eq fixedLeft) && (right eq fixedRight) => p

      // Main case (rebuild a resolution)
      case CutIC(left,right,pivot,_) => CutIC(fixedLeft, fixedRight, _ == pivot, true)
      
      // When the inference is not CutIC, nothing is done 
      case _ => p
    }
  }
}

abstract class AbstractRPIAlgorithm
extends AbstractRPILUAlgorithm {

  protected def safeLiteralsFromChild(childWithSafeLiterals: (SequentProofNode, IClause),
                                      parent: SequentProofNode, edgesToDelete: EdgesToDelete) =
    childWithSafeLiterals match {
      case (child @ CutIC(left,right,_,auxR), safeLiterals) if left  == parent => 
        if (edgesToDelete.isMarked(child,right)) safeLiterals else (safeLiterals + auxR)
      case (child @ CutIC(left,right,auxL,_), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child,left))  safeLiterals else (auxL +: safeLiterals)
      case (_,safeLiterals) => safeLiterals
      // Unchecked Inf case _ => throw new Exception("Unknown or impossible inference rule")
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
        case CutIC(_,_,auxL,_) if safeLiterals.suc contains auxL => edgesToDelete.markRightEdge(p)
        case CutIC(_,_,_,auxR) if safeLiterals.ant contains auxR => edgesToDelete.markLeftEdge(p)
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
    nodeCollection foldDown { (p: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
      val result = fixProofNodes(edgesToDelete)(p, fixedPremises)
      if (proofsToMap contains p) fixMap.update(p, result)
      result 
    }}
    fixMap
  }
}

trait Intersection
extends AbstractRPIAlgorithm {
  protected def computeSafeLiterals(proof: SequentProofNode,
                          childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
                          edgesToDelete: EdgesToDelete
                          ) : IClause =
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof)} match {
      case Nil  =>
        if (!childrensSafeLiterals.isEmpty) edgesToDelete.markBothEdges(proof)
        proof.conclusion.toSetSequent
      case h::t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) => acc intersect safeLiteralsFromChild(v, proof, edgesToDelete) }
    }
}
