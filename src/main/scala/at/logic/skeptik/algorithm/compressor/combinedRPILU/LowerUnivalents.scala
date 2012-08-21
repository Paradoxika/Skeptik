package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
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
    def apply(newNode: SequentProof, oldNode: SequentProof, children: List[SequentProof], loweredPivots: MClause):NodeKind = {
      val literals = activeLiteralsNotInLoweredPivots(oldNode, children, loweredPivots)
  //      println("Remaining Literals " + literals)
      (literals.ant.size, literals.suc.size) match {
        case (0,0) => DeletableNode
        case (1,0) => isTheOnlyValentLiteral(Left(literals.ant.head),  newNode, loweredPivots)
        case (0,1) => isTheOnlyValentLiteral(Right(literals.suc.head), newNode, loweredPivots)
        case _ => OrdinaryNode
      }
    }
    def apply(node: SequentProof, children: List[SequentProof], loweredPivots: MClause):NodeKind =
        apply(node, node, children, loweredPivots)

    private def activeLiteralsNotInLoweredPivots(oldNode: SequentProof, children: Seq[SequentProof], loweredPivots: MClause) = {
      val result = MClause()
      children.foreach { (child) =>
          child match {
          case CutIC(left, right, aux, _) if left  == oldNode =>
            if (!(loweredPivots.suc contains aux)) result += aux
          case CutIC(left, right, aux, _) if right == oldNode =>
            if (!(loweredPivots.ant contains aux)) aux =+: result
          case _ =>
          }
      }
      result
    }

    private def isTheOnlyValentLiteral(remainingLiteral: Either[E,E], node: SequentProof, loweredPivots: MClause) = {
      val (leftLiterals, rightLiterals) = (node.conclusion.ant.toSet -- loweredPivots.suc,
                                           node.conclusion.suc.toSet -- loweredPivots.ant)
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

  protected def fixProofAndLowerUnivalents(proof: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) = {

    var univalents = List[SequentProof]()
    val loweredPivots = MClause()

    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      val children = proof.childrenOf(oldProof) filter { child => !childIsMarkedToDeleteParent(child, oldProof, edgesToDelete) }
      isLowerableUnivalent(newProof, oldProof, children, loweredPivots) match {
        case LowerableUnivalent(_) => univalents ::= newProof ; deleteFromChildren(oldProof, proof, edgesToDelete)
        case DeletableNode => deleteFromChildren(oldProof, proof, edgesToDelete)
        case _ =>
      }
      newProof
    }
    val pseudoRoot = proof.foldDown(reconstructProof _)

    /* The pivot literal needed to reintroduce univalent clause's nodes can be
     * safely forgotten. The algorithm ensures the lowered pivots clause isn't
     * tautological and that all non-valent literal of a lowered node have
     * their dual in the lowered pivots clause.                              */
    univalents.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left, right)} catch {case e:Exception => left}
    }
  }

}

abstract class LowerUnivalents
extends AbstractRPILUAlgorithm with CollectUnivalentsDuringFixing with IdempotentAlgorithm[SequentProof] {

  def apply(proof: ProofNodeCollection[SequentProof]) =
    ProofNodeCollection(fixProofAndLowerUnivalents(proof, MMap[SequentProof,DeletedSide]()))

}

object LowerUnivalents
extends LowerUnivalents

abstract class LowerUnivalentsAfterRecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals with CollectUnivalentsDuringFixing with Intersection
{

  def apply(proof: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = collectEdgesToDelete(proof)
    ProofNodeCollection(fixProofAndLowerUnivalents(proof, edgesToDelete))
  }

}

object LowerUnivalentsAfterRecyclePivots
extends LowerUnivalentsAfterRecyclePivots with RepeatableWhileCompressingAlgorithm[SequentProof]

object IdempotentLowerUnivalentsAfterRecyclePivots
extends LowerUnivalentsAfterRecyclePivots with IdempotentAlgorithm[SequentProof]

abstract class LowerUnivalentsBeforeRecyclePivots
extends AbstractThreePassLower {

  protected def collectLowerables(proof: ProofNodeCollection[SequentProof]) = {
    val loweredPivots = MClause()
    var orderedUnivalents = List[SequentProof]()
    val univalentsSafeLiterals = MMap[SequentProof, IClause]()
    val univalentsValentLiteral = MMap[SequentProof, IClause]()

    val rootSafeLiterals = proof.foldRight (IClause()) { (node, safeLiterals) =>
      isLowerableUnivalent(node, proof.childrenOf(node), loweredPivots) match {
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

  def apply(proof: ProofNodeCollection[SequentProof]) = {

    // First pass
    val (rootSafeLiterals, orderedUnivalents, univalentsSafeLiterals, univalentsValentLiteral) = collectLowerables(proof)
//    val nbUnitChildren = orderedUnivalents.foldLeft(0) { (acc,node) => acc + proof.childrenOf(node).length }
//    println(orderedUnivalents.length + " orderedUnivalents with " + nbUnitChildren + " children" )

    // Second pass
    val edgesToDelete = collectEdgesToDelete(proof, rootSafeLiterals, univalentsSafeLiterals)
//    println(edgesToDelete.size + " edges to delete (" + (edgesToDelete.size - nbUnitChildren) + " without orderedUnivalents' children)")

    // Third pass
    if (edgesToDelete.isEmpty) proof else ProofNodeCollection({
      val fixMap = mapFixedProofs(orderedUnivalents.toSet + proof.root, edgesToDelete, proof)
      orderedUnivalents.foldLeft(fixMap(proof.root)) { (root, univalent) =>
        val valentLiteral = univalentsValentLiteral(univalent)
        if (valentLiteral.ant.isEmpty)
          CutIC(fixMap(univalent), root, _ == valentLiteral.suc.head, true)
        else
          CutIC(root, fixMap(univalent), _ == valentLiteral.ant.head, true)
      }
    })
  }

}

object LowerUnivalentsBeforeRecyclePivots
extends LowerUnivalentsBeforeRecyclePivots with RepeatableWhileCompressingAlgorithm[SequentProof]

object IdempotentLowerUnivalentsBeforeRecyclePivots
extends LowerUnivalentsBeforeRecyclePivots with IdempotentAlgorithm[SequentProof]
