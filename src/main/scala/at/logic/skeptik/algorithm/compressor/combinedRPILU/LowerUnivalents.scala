package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.mutable.{SetSequent => MClause}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

package lowerableUnivalent {

  abstract sealed class NodeKind
  case class  LowerableUnivalent (val valentLiteral: Either[E,E]) extends NodeKind
  case object DeletableNode extends NodeKind
  case object OrdinaryNode  extends NodeKind

  object isLowerableUnivalent
  {
    def apply(newProof: SequentProof, oldProof: SequentProof, children: List[SequentProof], loweredPivots: MClause):NodeKind = {
      val literals = activeLiteralsNotInLoweredPivots(newProof, oldProof, children, loweredPivots)
  //      println("Remaining Literals " + literals)
      (literals.ant.size, literals.suc.size) match {
        case (0,0) => DeletableNode
        case (1,0) => isTheOnlyValentLiteral(Left(literals.ant.head),  newProof, loweredPivots)
        case (0,1) => isTheOnlyValentLiteral(Right(literals.suc.head), newProof, loweredPivots)
        case _ => OrdinaryNode
      }
    }
    def apply(proof: SequentProof, children: List[SequentProof], loweredPivots: MClause):NodeKind =
        apply(proof, proof, children, loweredPivots)

    private def activeLiteralsNotInLoweredPivots(newProof: SequentProof, oldProof: SequentProof,
                                             children: Seq[SequentProof], loweredPivots: MClause) = {
      val result = MClause()
      children.foreach { (child) =>
          child match {
          case CutIC(left, right, aux, _) if left  == oldProof =>
            if (!(loweredPivots.suc contains aux)) result += aux
          case CutIC(left, right, aux, _) if right == oldProof =>
            if (!(loweredPivots.ant contains aux)) aux =+: result
          case _ =>
          }
      }
      result
    }

    private def isTheOnlyValentLiteral(remainingLiteral: Either[E,E], proof: SequentProof, loweredPivots: MClause) = {
      val (leftLiterals, rightLiterals) = (proof.conclusion.ant.toSet -- loweredPivots.suc,
                                           proof.conclusion.suc.toSet -- loweredPivots.ant)
      (leftLiterals.size, rightLiterals.size, remainingLiteral) match {
        case (1,0,Left(literal))  if leftLiterals.head  == literal => literal =+: loweredPivots ; LowerableUnivalent(remainingLiteral)
        case (0,1,Right(literal)) if rightLiterals.head == literal => loweredPivots += literal  ; LowerableUnivalent(remainingLiteral)
        case _ => OrdinaryNode
      }
    }

  } // object isLowerableUnivalent
} // package lowerableUnivalent

import lowerableUnivalent._

trait CollectUnivalentsDuringFixing
extends AbstractRPILUAlgorithm {

  protected def fixProofAndLowerUnivalents(nodeCollection: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) = {

    var univalents = List[SequentProof]()
    val loweredPivots = MClause()

    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      val children = nodeCollection.childrenOf(oldProof) filter { child => !childIsMarkedToDeleteParent(child, oldProof, edgesToDelete) }
      isLowerableUnivalent(newProof, oldProof, children, loweredPivots) match {
        case LowerableUnivalent(_) => univalents ::= newProof ; deleteFromChildren(oldProof, nodeCollection, edgesToDelete)
        case DeletableNode => deleteFromChildren(oldProof, nodeCollection, edgesToDelete)
        case _ =>
      }
      newProof
    }
    val pseudoRoot = nodeCollection.foldDown(reconstructProof _)

    /* The pivot literal needed to reintroduce univalent clause's nodes can be
     * safely forgotten. The algorithm ensures the lowered pivots clause isn't
     * tautological and that all non-valent literal of a lowered node have
     * their dual in the lowered pivots clause.                              */
    univalents.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left, right)} catch {case e:Exception => left}
    }
  }

}

class LowerUnivalents
extends AbstractRPILUAlgorithm with CollectUnivalentsDuringFixing {

  def apply(proof: SequentProof): SequentProof =
    fixProofAndLowerUnivalents(ProofNodeCollection(proof), MMap[SequentProof,DeletedSide]())

}

class LowerUnivalentsAfterRecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals with CollectUnivalentsDuringFixing with Intersection {

  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(nodeCollection)
    fixProofAndLowerUnivalents(nodeCollection, edgesToDelete)
  }

}

/* Still bogus :
 * QG-classification/qg5/iso_brn038.smt2
 * QG-classification/qg5/iso_brn457.smt2
 * QG-classification/qg5/iso_brn1281.smt2
 * QG-classification/qg5/iso_icl1118.smt2
 * QG-classification/qg5/iso_icl1118.smt2
 */
//class LowerUnivalentsBeforeRecyclePivots
//extends AbstractThreePassLower {
//
//  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]) = {
//    val loweredPivots = MClause()
//    var univalents = List[SequentProof]()
//    val map = MMap[SequentProof, (IClause,IClause)]()
//
//    val rootSafeLiterals = nodeCollection.foldRight (IClause()) { (p, safeLiterals) =>
//      isLowerableUnivalent(p, nodeCollection.childrenOf(p), loweredPivots) match {
//        // TODO : should I add the valent literal to safeLiterals to be transmited to premises ?
//        case LowerableUnivalent(Left(l))  =>
//          univalents ::= p
//          map.update(p, (new IClause(Set[E](l),Set[E]()), safeLiterals))
//          safeLiterals + l
//        case LowerableUnivalent(Right(l)) =>
//          univalents ::= p
//          map.update(p, (new IClause(Set[E](),Set[E](l)), safeLiterals))
//          l +: safeLiterals
//        case _ => safeLiterals
//      }
//    }
//    (rootSafeLiterals, univalents, map)
//  }
//
//  override protected def collectEdgesToDelete(nodeCollection: ProofNodeCollection[SequentProof],
//                                              rootSafeLiterals: IClause,
//                                              unitsMap: Map[SequentProof,(IClause,IClause)]) = {
//    val edgesToDelete = MMap[SequentProof,DeletedSide]()
//    val protectedLiteralMap = MMap[SequentProof,IClause]()
//
//    // Scala doesn't want the following inner function to be called visit like in the overriden method :
//    // "java.lang.VerifyError: class LowerUnivalentsBeforeRecyclePivots overrides final method visit$1"
//    def visitW(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
//
//      // Node is lowerable
//      if (unitsMap contains p) {
//  //        println("Unit " + p.conclusion + " " + unitsMap(p))
//        val (efficientLiteral, safeLiteralsForUnit) = unitsMap(p)
//        if (protectedLiteralMap contains p) {
//          val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete) intersect safeLiteralsForUnit
//          computeEdgesToDeleteAndProtectedLiterals(p, safeLiterals, edgesToDelete, protectedLiteralMap)
//          (p, safeLiterals)
//        }
//        else {
//          deleteFromChildren(p, nodeCollection, edgesToDelete)
//          p.premises.foreach (addProtectedLiterals(efficientLiteral, _, protectedLiteralMap))
//          (p, safeLiteralsForUnit)
//        }
//      }
//
//      // Root node
//      else if (childrensSafeLiterals == Nil) (p, rootSafeLiterals)
//
//      else {
//        val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
//        computeEdgesToDeleteAndProtectedLiterals(p, safeLiterals, edgesToDelete, protectedLiteralMap)
//        (p, safeLiterals)
//      }
//    }
//
//    nodeCollection.bottomUp(visitW)
//    edgesToDelete
//  }
//
//}
