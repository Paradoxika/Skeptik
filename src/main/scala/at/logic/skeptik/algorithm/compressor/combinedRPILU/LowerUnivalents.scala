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
    def apply(clause: IClause, oldProof: SequentProof, children: List[SequentProof], loweredPivots: MClause):NodeKind = {
      val literals = activeLiteralsNotInLoweredPivots(oldProof, children, loweredPivots)
  //      println("Remaining Literals " + literals)
      (literals.ant.size, literals.suc.size) match {
        case (0,0) => DeletableNode
        case (1,0) => isTheOnlyValentLiteral(Left(literals.ant.head),  clause, loweredPivots)
        case (0,1) => isTheOnlyValentLiteral(Right(literals.suc.head), clause, loweredPivots)
        case _ => OrdinaryNode
      }
    }
    def apply(newProof: SequentProof, oldProof: SequentProof, children: List[SequentProof], loweredPivots: MClause):NodeKind =
      apply(IClause(newProof.conclusion), oldProof, children, loweredPivots)
    def apply(proof: SequentProof, children: List[SequentProof], loweredPivots: MClause):NodeKind =
      apply(IClause(proof.conclusion), proof, children, loweredPivots)

    private def activeLiteralsNotInLoweredPivots(oldProof: SequentProof, children: Seq[SequentProof], loweredPivots: MClause) = {
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

    private def isTheOnlyValentLiteral(remainingLiteral: Either[E,E], clause: IClause, loweredPivots: MClause) = {
      val (leftLiterals, rightLiterals) = (clause.ant -- loweredPivots.suc,
                                           clause.suc -- loweredPivots.ant)
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

/* Still bogus (2012/08/02) :
 * QG-classification/qg5/iso_brn1281.smt2
 * QG-classification/qg5/iso_icl1118.smt2
 *
 * QG-classification/loops6/iso_icl092.smt2
 * QG-classification/loops6/iso_icl042.smt2
 * QG-classification/qg5/iso_icl219.smt2
 * QG-classification/qg5/iso_icl218.smt2
 *
 * QG-classification/qg5/iso_icl055.smt2
 */
class LowerUnivalentsBeforeRecyclePivots
extends AbstractThreePassLower {

  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val loweredPivots = MClause()
    var univalents = List[SequentProof]()
    val map = MMap[SequentProof, (IClause,IClause)]()
    var rootSafeLiterals = IClause()

    def visit(node: SequentProof, premiseDeletedLiterals: List[IClause]) = {
      val deletedLiterals = node match {
        // It is assumed here that in case when no premises contain the pivot, the left one will be kept during fixing.

        case CutIC(left, right, pivot,_) if (map contains right) || ((premiseDeletedLiterals(0).suc contains pivot) && !(map contains left)) =>
          println("Del right " + right.conclusion + " pivot " + pivot + " left " + left.conclusion + " deleted " + premiseDeletedLiterals(0))
          premiseDeletedLiterals(0) ++ IClause(right.conclusion) -- new IClause(Set(pivot),Set(pivot))

        case CutIC(left, right, pivot,_) if (map contains left) || (premiseDeletedLiterals(1).ant contains pivot) =>
          println("Del left " + left.conclusion + " pivot " + pivot + " right " + right.conclusion + " deleted " + premiseDeletedLiterals(1))
          premiseDeletedLiterals(1) ++ IClause(left.conclusion) -- new IClause(Set(pivot),Set(pivot))

        case CutIC(left,right,_,_) =>
          (premiseDeletedLiterals(0) -- IClause(right.conclusion)) ++
          (premiseDeletedLiterals(1) -- IClause(left.conclusion))  ++
          (premiseDeletedLiterals(0) intersect premiseDeletedLiterals(1))

        case Axiom(_) =>
          IClause()
      }
      if (node.isInstanceOf[CutIC] && !deletedLiterals.isFalse) println("Deleted " + deletedLiterals)
      val conclusion = IClause(node.conclusion) -- deletedLiterals

      isLowerableUnivalent(conclusion, node, nodeCollection.childrenOf(node), loweredPivots) match {
        // TODO : should I add the valent literal to safeLiterals to be transmited to premises ?
        case LowerableUnivalent(Left(l))  =>
          println("Uni " + node.conclusion + " as " + conclusion)
          univalents ::= node
          map.update(node, (new IClause(Set[E](l),Set[E]()), rootSafeLiterals))
          rootSafeLiterals = rootSafeLiterals + l
        case LowerableUnivalent(Right(l)) =>
          println("Uni " + node.conclusion + " as " + conclusion)
          univalents ::= node
          map.update(node, (new IClause(Set[E](),Set[E](l)), rootSafeLiterals))
          rootSafeLiterals = l +: rootSafeLiterals
        case _ =>
      }

      deletedLiterals
    }

    nodeCollection.foldDown(visit)
    (rootSafeLiterals, univalents, map)
  }

}
