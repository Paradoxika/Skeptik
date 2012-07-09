package skeptik.algorithm.compressor

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.judgment.immutable.{SetSequent => IClause}
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.Map

abstract class AbstractRPILUAlgorithm
extends Function1[SequentProof,SequentProof] {

  protected sealed abstract  class DeletedSide
  protected object LeftDS  extends DeletedSide
  protected object RightDS extends DeletedSide

  // Abtsract functions

  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof

  // Utility functions

  def childIsMarkedToDeleteParent(child: SequentProof, parent: SequentProof, edgesToDelete: Map[SequentProof,DeletedSide]) =
    (edgesToDelete contains child) &&
    (edgesToDelete(child) match {
      case LeftDS  => parent == child.premises(0)
      case RightDS => parent == child.premises(1)
    })

  def sideOf(parent: SequentProof, child: SequentProof) = child match {
    // TODO: use premises like above
    case CutIC(left, right, _,_) if parent == left  => LeftDS
    case CutIC(left, right, _,_) if parent == right => RightDS
    case _ => throw new Exception("Unable to find parent in child")
  }

  // A faster size
  def fakeSize[A](l: List[A]) = l match {
    case Nil => 0
    case _::Nil => 1
    case _::_ => 2
  }

  def isUnit(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof]) =
    (fakeSize(proof.conclusion.ant) + fakeSize(proof.conclusion.suc) == 1) &&
    (fakeSize(nodeCollection.childrenOf(proof)) > 1)

  def deleteFromChildren(oldProof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) =
    nodeCollection.childrenOf(oldProof).foreach { child =>
      // Deleting both premises of a node being too complicated, regularization takes precedence over unit lowering.
      if (!(edgesToDelete contains child)) edgesToDelete.update(child, sideOf(oldProof, child))
    }

  // Main functions

  def fixProofs(edgesToDelete: Map[SequentProof,DeletedSide])
               (p: SequentProof, fixedPremises: List[SequentProof]) = {
    lazy val fixedLeft  = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => Axiom(conclusion)
      case CutIC(left,right,_,_) if edgesToDelete contains p => edgesToDelete(p) match {
        case LeftDS  => fixedRight
        case RightDS => fixedLeft
      }
      case CutIC(left,right,auxL,auxR) => ((fixedLeft.conclusion.suc  contains auxL),
                                           (fixedRight.conclusion.ant contains auxR)) match {
        case (true,true) => CutIC(fixedLeft, fixedRight, _ == auxL)
        case (true,false) => fixedRight
        case (false,true) => fixedLeft
        case (false,false) => heuristicChoose(fixedLeft, fixedRight)
      }
    }
  }
}

abstract class AbstractRPIAlgorithm
extends AbstractRPILUAlgorithm {
  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, IClause)],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, IClause)) => IClause
                          ) : IClause
}

trait CollectEdgesUsingSafeLiterals
extends AbstractRPIAlgorithm {
  def collectEdgesToDelete(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      def safeLiteralsFromChild(v:(SequentProof, IClause)) = v match {
        case (p, safeLiterals) if edgesToDelete contains p => safeLiterals
        case (CutIC(left,_,_,auxR),  safeLiterals) if left  == p => safeLiterals + auxR
        case (CutIC(_,right,auxL,_), safeLiterals) if right == p => auxL +: safeLiterals
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
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
  def mapFixedProofs(proofsToMap: Set[SequentProof],
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
  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, IClause)],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, IClause)) => IClause
                          ) : IClause = {
    childrensSafeLiterals.filter { x => !childIsMarkedToDeleteParent(x._1, proof, edgesToDelete)} match {
      case Nil  => IClause(proof.conclusion)
      case h::t => t.foldLeft(safeLiteralsFromChild(h)) { (acc, v) => acc intersect safeLiteralsFromChild(v) }
    }
  }
}

trait LeftHeuristic
extends AbstractRPILUAlgorithm {
  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof = left
}

