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
          deleteNode(node)
          true
        //        case UnifyingResolutionMRR(left, right, _, _) if (isMarked(node, left) && isMarked(node, right)) =>
        //          deleteNode(node)
        //          true          
        case _ => false
      }
    }

    //TODO: do I need to match MRR nodes? probably.
    protected def sideOf(parent: SequentProofNode, child: SequentProofNode) = child match {
      case UnifyingResolution(left, right, _, _) => if (parent == left) LeftDS
      else if (parent == right) RightDS
      else throw new Exception("Unable to find parent in child")

      //      case UnifyingResolutionMRR(left, right, _, _) => if (parent == left) LeftDS
      //      else if (parent == right) RightDS
      //      else throw new Exception("Unable to find parent in child")

      case _ => throw new Exception("This function should never be called with child not being a UR")
    }

  }

  // Main functions
  //TODO: do I need to match MRR nodes? probably.
  protected def fixProofNodes(edgesToDelete: EdgesToDelete, unifiableVariables: MSet[Var])(p: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
    lazy val fixedLeft = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => p

      // If we've got a proof of false, we propagate it down the proof
      case UnifyingResolution(_, _, _, _) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) => {
        fixedLeft
      }

      case UnifyingResolution(_, _, _, _) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) => {
        fixedRight
      }

      // Delete nodes and edges
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, left) => {
        fixedRight
      }
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, right) => {
        fixedLeft
      }

      // If premises haven't been changed, we keep the proof as is (memory optimization)
      case UnifyingResolution(left, right, _, _) if (left eq fixedLeft) && (right eq fixedRight) => p

      // Main case (rebuild a resolution)
      case UnifyingResolution(left, right, pivot, _) => {
        try {
          try {
            UnifyingResolutionMRR(fixedRight, fixedLeft)(unifiableVariables)
          } catch {
            case e: Exception => {
              UnifyingResolutionMRR(fixedLeft, fixedRight)(unifiableVariables)
            }
          }
        } catch {
          //TODO: can I always just replace it with the one on the left? This seems sketchy.
          //See skype conversation:
          // "When a fixed parent p of a node n does not contain the pivot it should contain, then n should be replaced by p ."
          //TODO: implement that.
          case e: Exception => {
            println("pivot: " + pivot)
            println(" fixedLeft: " + fixedLeft + " and fixedRight: " + fixedRight)
            println(" left: " + left + " and right: " + right)
            println(UnifyingResolutionMRR(left, right)(unifiableVariables))
            fixedLeft
          }
        }
      }

      // When the inference is not UR, nothing is done 
      case _ => {
        p
      }
    }
  }
}

abstract class FOAbstractRPIAlgorithm
  extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  protected def safeLiteralsFromChild(childWithSafeLiterals: (SequentProofNode, IClause),
    parent: SequentProofNode, edgesToDelete: EdgesToDelete) =
    childWithSafeLiterals match {
      case (child @ UnifyingResolution(left, right, _, auxR), safeLiterals) if left == parent =>
        if (edgesToDelete.isMarked(child, right)) safeLiterals else  addLiteralSmart(safeLiterals, auxR, false, left, right)
      case (child @ UnifyingResolution(left, right, auxL, _), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child, left)) safeLiterals else  addLiteralSmart(safeLiterals, auxL, true, left, right)

      case (_, safeLiterals) => safeLiterals
      // Unchecked Inf case _ => throw new Exception("Unknown or impossible inference rule")
    }

  protected def addLiteralSmart(seq: IClause, aux: E, addToAntecedent: Boolean, left: SequentProofNode, right: SequentProofNode): IClause = {
    val uVars = new MSet[Var]() union getSetOfVars(left) union getSetOfVars(right)
    val seqHalf = if (addToAntecedent) {
      seq.ant 
    } else {
      seq.suc
    }
    for (lit <- seqHalf) {
      unify((lit, aux) :: Nil)(uVars) match {
        case None => {}
        case Some(_) => { return seq }
      }
    }
    if(addToAntecedent) {
      aux +: seq
    } else { 
      seq + aux
    }
  }
  
  protected def computeSafeLiterals(proof: SequentProofNode,
    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
    edgesToDelete: EdgesToDelete): IClause

}

trait FOCollectEdgesUsingSafeLiterals
  extends FOAbstractRPIAlgorithm with CanRenameVariables {

  protected def checkForRes(safeLiteralsHalf: Set[E], aux: E, unifiableVars: MSet[Var]): Boolean = {

    //TODO: unifiableVars might not contain the variables in the aux formulae. There is a workaround implemented below,
    //but there's probably a better way to do this.
    if (safeLiteralsHalf.size < 1) {
      return false
    }

    for (safeLit <- safeLiteralsHalf) {
      unify((aux, safeLit) :: Nil)(unifiableVars union getSetOfVars(Axiom(Sequent(aux)()))) match {
        case Some(_) => {
          return true
        }
        case None => {
          //Do nothing
        }
      }
    }
    false
  }

  protected def getAllVars(proof: Proof[SequentProofNode]): MSet[Var] = {
    var out = MSet[Var]()
    for (n <- proof) {
      out = out union getSetOfVars(n)
    }
    out
  }

  protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode], unifiableVars: MSet[Var]) = {
    val edgesToDelete = new EdgesToDelete()

    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      p match {
        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.suc, auxL, unifiableVars)) => {
          edgesToDelete.markRightEdge(p)

        }
        case UnifyingResolution(left, right, auxL, auxR) if checkForRes(safeLiterals.ant, auxR, unifiableVars) => {
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
}

//TODO: do we want to contract things in the intersection to save memory?
trait FOIntersection
  extends FOAbstractRPIAlgorithm {
  protected def computeSafeLiterals(proof: SequentProofNode,
    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
    edgesToDelete: EdgesToDelete): IClause = {
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof) } match {
      case Nil =>
        if (!childrensSafeLiterals.isEmpty) edgesToDelete.markBothEdges(proof)
        proof.conclusion.toSetSequent
      case h :: t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) => acc intersect safeLiteralsFromChild(v, proof, edgesToDelete) }
    }
  }
}
