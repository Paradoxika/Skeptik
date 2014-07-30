package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.judgment.immutable.{ SetSequent => IClause }
import at.logic.skeptik.expression._
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import collection.Map
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.Contraction
import at.logic.skeptik.proof.sequent.resolution.CanRenameVariables
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }

abstract class FOAbstractRPILUAlgorithm
  extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {

  class EdgesToDelete {

    protected sealed abstract class DeletedSide
    protected case object NoDS extends DeletedSide
    protected case object LeftDS extends DeletedSide
    protected case object RightDS extends DeletedSide
    protected case object BothDS extends DeletedSide

    val edges = MMap[SequentProofNode, (DeletedSide, Boolean)]()

    private def otherSide(side: DeletedSide) = side match {
      case LeftDS => RightDS
      case RightDS => LeftDS
      case _ => NoDS
    }

    def markEdge(node: SequentProofNode, premiseSide: DeletedSide) = {
      edges(node) = edges.get(node) match {
        case None => (premiseSide, false)
        case Some((BothDS, _)) => (BothDS, true)
        case Some((side, _)) if side == otherSide(premiseSide) => (BothDS, true)
        case Some((_, del)) => (premiseSide, del)
      }
    }

    def markEdge(child: SequentProofNode, premise: SequentProofNode): Unit =
      markEdge(child, sideOf(premise, child))

    def markBothEdges(node: SequentProofNode) = { edges(node) = (BothDS, true) }

    def markLeftEdge(node: SequentProofNode) = markEdge(node, LeftDS)

    def markRightEdge(node: SequentProofNode) = markEdge(node, RightDS)

    def deleteNode(node: SequentProofNode) =
      edges(node) = (edges.getOrElse(node, (NoDS, true))._1, true)

    def deletedSide(node: SequentProofNode) =
      edges.get(node) match {
        case Some((NoDS, _)) => None
        case Some((s, _)) => Some(s)
        case None => None
      }

    def isEmpty = edges.isEmpty

    def isMarked(node: SequentProofNode, premise: SequentProofNode): Boolean = {
      (edges.get(node) match {
        case None => false
        case Some((BothDS, _)) => true
        case Some((NoDS, true)) => false
        case Some((side, _)) => side == sideOf(premise, node)
      }) || nodeIsMarked(premise)
    }

    def nodeIsMarked(node: SequentProofNode): Boolean = {
      // may be optimized (edgesToDelete contains node is checked 3 times)
      node match {
        case _ if ((edges contains node) && edges(node)._2) => true
        //        case R(left, right, _, _) if (isMarked(node, left) && isMarked(node, right)) =>
        case UnifyingResolution(left, right, _, _) if (isMarked(node, left) && isMarked(node, right)) =>
          //          println("Case B")
          deleteNode(node)
          true
        case _ => false
      }
    }

    protected def sideOf(parent: SequentProofNode, child: SequentProofNode) = child match {
      case UnifyingResolution(left, right, _, _) => if (parent == left) LeftDS
      else if (parent == right) RightDS
      else throw new Exception("Unable to find parent in child")
      case _ => throw new Exception("This function should never be called with child not being a UR")
    }

  }

  // Utility functions

  protected def isUnit(proof: SequentProofNode, nodeCollection: Proof[SequentProofNode]) =
    (proof.conclusion.ant.length + proof.conclusion.suc.length == 1) &&
      (nodeCollection.childrenOf(proof).length > 1)

  // Main functions

      
  //TODO: the error that I think is below, might be here instead: fixedPremises might not be updating correctly.
  protected def fixProofNodes(edgesToDelete: EdgesToDelete, unifiableVariables: MSet[Var])(p: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
    println("fixedPremises: " + fixedPremises)
    lazy val fixedLeft = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => p

      // If we've got a proof of false, we propagate it down the proof
      //      case R(_, _, _, _) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) =>
      case UnifyingResolution(_, _, _, _) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) => {
//        println("A")
        fixedLeft
      }        
        
      //      case R(_, _, _, _) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) =>
      case UnifyingResolution(_, _, _, _) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) =>{ 
//        println("B")
        fixedRight
      }

      // Delete nodes and edges
      
      //TODO: note that I changed fixedRight to fixedLeft, and vice versa,
      //when compared with the non-FO version. Is this necessary?
      
      //      case R(left, right, _, _) if edgesToDelete.isMarked(p, left) =>
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, left) => {
//        println("C")
        println("replacing with: " + fixedLeft)
        fixedLeft
        //fixedRight
      }
      //      case R(left, right, _, _) if edgesToDelete.isMarked(p, right) =>
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, right) => {
//        println("D")
        fixedRight
        //fixedLeft
      }

      // If premises haven't been changed, we keep the proof as is (memory optimization)
      //      case R(left, right, _, _) if (left eq fixedLeft) && (right eq fixedRight) => p
      case UnifyingResolution(left, right, _, _) if (left eq fixedLeft) && (right eq fixedRight) => p

      // Main case (rebuild a resolution)
      //      case R(left, right, pivot, _) => R(fixedLeft, fixedRight, pivot, true)
      case UnifyingResolution(left, right, pivot, _) => {
//        println("r: " + right + " and l: " + left)
        println("fr: " + fixedRight + " and fl: " + fixedLeft + " (" + unifiableVariables +")")
        try {
           UnifyingResolutionMRR(fixedRight, fixedLeft)(unifiableVariables)
         // UnifyingResolution( left, right)(unifiableVariables)
        } catch {
          case e: Exception => {
            UnifyingResolutionMRR(fixedLeft, fixedRight)(unifiableVariables)  
          }
        }
      }

      // When the inference is not R, nothing is done 
      case _ => p
    }
  }
}

abstract class FOAbstractRPIAlgorithm
  extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  protected def safeLiteralsFromChild(childWithSafeLiterals: (SequentProofNode, IClause),
    parent: SequentProofNode, edgesToDelete: EdgesToDelete) =
    childWithSafeLiterals match {
      //      case (child @ R(left,right,_,auxR), safeLiterals) if left  == parent => 
      //        if (edgesToDelete.isMarked(child,right)) safeLiterals else (safeLiterals + auxR)
      //      case (child @ R(left,right,auxL,_), safeLiterals) if right == parent =>
      //        if (edgesToDelete.isMarked(child,left))  safeLiterals else (auxL +: safeLiterals)
      case (child @ UnifyingResolution(left, right, _, auxR), safeLiterals) if left == parent =>
        if (edgesToDelete.isMarked(child, right)) safeLiterals else addLiteralSmart(safeLiterals, auxR, left, right) //(safeLiterals + auxR)
      case (child @ UnifyingResolution(left, right, auxL, _), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child, left)) safeLiterals else addLiteralSmartB(safeLiterals, auxL, left, right) //(auxL +: safeLiterals)

      case (_, safeLiterals) => safeLiterals
      // Unchecked Inf case _ => throw new Exception("Unknown or impossible inference rule")
    }

  //TODO: can merge these two functions? or at least do it smarter?
  protected def addLiteralSmart(seq: IClause, auxR: E, left: SequentProofNode, right: SequentProofNode): IClause = {
    val uVars = new MSet[Var]() union getSetOfVars(left) union getSetOfVars(right)
    for (lit <- seq.suc) {
      unify((lit, auxR) :: Nil)(uVars) match {
        case None => {}
        case Some(_) => { return seq }
      }
    }
    seq + auxR
  }

  protected def addLiteralSmartB(seq: IClause, auxL: E, left: SequentProofNode, right: SequentProofNode): IClause = {
    val uVars = new MSet[Var]() union getSetOfVars(left) union getSetOfVars(right)
    for (lit <- seq.ant) {
      unify((lit, auxL) :: Nil)(uVars) match {
        case None => {}
        case Some(_) => { return seq }
      }
    }
    auxL +: seq
  }

  protected def computeSafeLiterals(proof: SequentProofNode,
    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
    edgesToDelete: EdgesToDelete): IClause

}

trait FOCollectEdgesUsingSafeLiterals
  extends FOAbstractRPIAlgorithm with CanRenameVariables {

  
  //TODO: error here (or when it's called)
  protected def checkForRes(safeLiteralsHalf: Set[E], isAntecedent: Boolean, auxL: E, auxR: E, unifiableVars: MSet[Var]): Boolean = {
    
    if (safeLiteralsHalf.size < 1) {
      return false
    }

    println("safe: (" + isAntecedent + ") " + safeLiteralsHalf)
    //    println("pivot: " + auxL + " and " + auxR)
    
    for (safeLit <- safeLiteralsHalf) {
      println("attempting to unify " + safeLit + " and " + auxL + " using " +  unifiableVars)
      unify((auxL, safeLit) :: Nil)(unifiableVars) match {
        case Some(_) => {
          return true
        }
        case None => {
           return false
        }
      }
    }
    //true 
    false
  }

  protected def getAllVars(proof: Proof[SequentProofNode]): MSet[Var] = {
    var out = MSet[Var]()
    for (n <- proof) {
      out = out union getSetOfVars(n)
    }
    out
  }

  protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
    val edgesToDelete = new EdgesToDelete()

    val unifiableVars = getAllVars(nodeCollection);

    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      //      println(safeLiterals + " are safe for " + p)
      p match {
        //        case R(_,_,auxL,_) if safeLiterals.suc contains auxL => edgesToDelete.markRightEdge(p)
        //        case R(_,_,_,auxR) if safeLiterals.ant contains auxR => edgesToDelete.markLeftEdge(p)
        //TODO: check
        //      case UnifyingResolution(left, right, _, _) if safeLiterals.suc contains left.conclusion.toSetSequent.suc.head => {
        case UnifyingResolution(left, right, auxL, auxR) if checkForRes(safeLiterals.suc, false, auxL, auxR, unifiableVars) => {
          println("left: " + left)
          println("right: " + right)
          println("auxL: " + auxL)
          //println("auxR: " + auxR)
          println("MARKED l: " + p)
          edgesToDelete.markLeftEdge(p)
        }
        //        case UnifyingResolution(left, right, _, _) if safeLiterals.ant contains right.conclusion.toSetSequent.ant.head => {
        case UnifyingResolution(left, right, auxL, auxR) if checkForRes(safeLiterals.ant, true, auxR, auxL, unifiableVars) => {

                    println("MARKED r: " + p)
          edgesToDelete.markLeftEdge(p)
        }

        case _ =>
      }
      (p, safeLiterals)
    }
    nodeCollection.bottomUp(visit)
    edgesToDelete
  }
}

trait FOUnitsCollectingBeforeFixing
  extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  protected def getAllVars(proof: Proof[SequentProofNode]): MSet[Var] = {
    var out = MSet[Var]()
    for (n <- proof) {
      out = out union getSetOfVars(n)
    }
    out
  }

  //this code is not used?
//  protected def mapFixedProofNodes(proofsToMap: Set[SequentProofNode],
//    edgesToDelete: EdgesToDelete,
//    nodeCollection: Proof[SequentProofNode]) = {
//    val fixMap = MMap[SequentProofNode, SequentProofNode]()
//    val unifiableVars = getAllVars(nodeCollection);
//
//    nodeCollection foldDown { (p: SequentProofNode, fixedPremises: Seq[SequentProofNode]) =>
//      {
//        val result = fixProofNodes(edgesToDelete,  unifiableVars)(p, fixedPremises)
//        if (proofsToMap contains p) {
//          println("updating " + p + " ---> " + result)
//          fixMap.update(p, result)
//        }
//        result
//      }
//    }
//    fixMap
//  }
}

trait FOIntersection
  extends FOAbstractRPIAlgorithm {
  protected def computeSafeLiterals(proof: SequentProofNode,
    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
    edgesToDelete: EdgesToDelete): IClause =
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof) } match {
      case Nil =>
        if (!childrensSafeLiterals.isEmpty) edgesToDelete.markBothEdges(proof)
        proof.conclusion.toSetSequent
      case h :: t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) => acc intersect safeLiteralsFromChild(v, proof, edgesToDelete) }
    }
}
