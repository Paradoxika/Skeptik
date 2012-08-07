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
      val literals = activeLiteralsNotInLoweredPivots(oldProof, children, loweredPivots)
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
class LowerUnivalentsBeforeRecyclePivots
extends AbstractThreePassLower {

  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val loweredPivots = MClause()
    var orderedUnivalents = List[SequentProof]()
    val univalentsSafeLiterals = MMap[SequentProof, IClause]()
    val univalentsValentLiteral = MMap[SequentProof, IClause]()

    val rootSafeLiterals = nodeCollection.foldRight (IClause()) { (node, safeLiterals) =>
      isLowerableUnivalent(node, nodeCollection.childrenOf(node), loweredPivots) match {
        case LowerableUnivalent(Left(l))  =>
          orderedUnivalents ::= node
          univalentsValentLiteral.update(node, new IClause(Set(l),Set()))
          univalentsSafeLiterals.update(node, l +: safeLiterals)
          safeLiterals + l
        case LowerableUnivalent(Right(l)) =>
          orderedUnivalents ::= node
          univalentsValentLiteral.update(node, new IClause(Set(),Set(l)))
          univalentsSafeLiterals.update(node, safeLiterals + l)
          l +: safeLiterals
        case _ => safeLiterals
      }
    }
    (rootSafeLiterals, orderedUnivalents, univalentsSafeLiterals, univalentsValentLiteral)
  }

  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)

    // First pass
    val (rootSafeLiterals, orderedUnivalents, univalentsSafeLiterals, univalentsValentLiteral) = collectLowerables(nodeCollection)
//    val nbUnitChildren = orderedUnivalents.foldLeft(0) { (acc,node) => acc + nodeCollection.childrenOf(node).length }
//    println(orderedUnivalents.length + " orderedUnivalents with " + nbUnitChildren + " children" )

    // Second pass
    val edgesToDelete = collectEdgesToDelete(nodeCollection, rootSafeLiterals, univalentsSafeLiterals)
//    println(edgesToDelete.size + " edges to delete (" + (edgesToDelete.size - nbUnitChildren) + " without orderedUnivalents' children)")

    // Third pass
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(orderedUnivalents.toSet + proof, edgesToDelete, nodeCollection)
      orderedUnivalents.foldLeft(fixMap(proof)) { (root, univalent) =>
        val valentLiteral = univalentsValentLiteral(univalent)
        if (valentLiteral.ant.isEmpty)
          CutIC(fixMap(univalent), root, _ == valentLiteral.suc.head, true)
        else
          CutIC(root, fixMap(univalent), _ == valentLiteral.ant.head, true)
      }
    }
  }

}
