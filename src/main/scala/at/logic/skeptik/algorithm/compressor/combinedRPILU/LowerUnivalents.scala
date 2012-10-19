package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.Proof
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
    def apply(newNode: SequentProofNode, oldNode: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause,
              delete: (SequentProofNode,SequentProofNode) => Unit = (_:SequentProofNode,_:SequentProofNode) => Unit ):NodeKind = {
      val literals = activeLiteralsNotInLoweredPivots(oldNode, children, loweredPivots, delete)
  //      println("Remaining Literals " + literals)
      (literals.ant.size, literals.suc.size) match {
        case (0,0) => DeletableNode
        case (1,0) => isTheOnlyValentLiteral(Left(literals.ant.head),  newNode, loweredPivots)
        case (0,1) => isTheOnlyValentLiteral(Right(literals.suc.head), newNode, loweredPivots)
        case _ => OrdinaryNode
      }
    }
    def apply(node: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause):NodeKind =
        apply(node, node, children, loweredPivots)

    private def activeLiteralsNotInLoweredPivots(oldNode: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause,
                                                 delete: (SequentProofNode,SequentProofNode) => Unit) = {
      val result = MClause()
      children.foreach { (child) =>
          child match {
          case CutIC(left, right, aux, _) if left  == oldNode =>
            if (loweredPivots.suc contains aux) delete(child,left)  else result += aux
          case CutIC(left, right, aux, _) if right == oldNode =>
            if (loweredPivots.ant contains aux) delete(child,right) else aux =+: result
          case _ =>
          }
      }
      result
    }

    private def isTheOnlyValentLiteral(remainingLiteral: Either[E,E], node: SequentProofNode, loweredPivots: MClause) = {
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

  protected def fixProofAndLowerUnivalents(proof: Proof[SequentProofNode], edgesToDelete: EdgesToDelete) = {

    var univalents = List[SequentProofNode]()
    val loweredPivots = MClause()

    def fixResolutionAndDeleteUnivalent(oldNode: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
      val newNode = fixProofNodes(edgesToDelete)(oldNode, fixedPremises)
      val children = proof.childrenOf(oldNode) filter { child => !edgesToDelete.isMarked(child, oldNode) }
      isLowerableUnivalent(newNode, oldNode, children, loweredPivots) match {
        case LowerableUnivalent(_) => univalents ::= newNode ; edgesToDelete.deleteNode(oldNode)
        case DeletableNode => edgesToDelete.deleteNode(oldNode)
        case _ =>
      }
      newNode
    }
    val pseudoRoot = proof.foldDown(fixResolutionAndDeleteUnivalent _)

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
extends AbstractRPILUAlgorithm with CollectUnivalentsDuringFixing with IdempotentAlgorithm[SequentProofNode] {

  def apply(proof: Proof[SequentProofNode]) =
    Proof(fixProofAndLowerUnivalents(proof, new EdgesToDelete()))

}

object LowerUnivalents
extends LowerUnivalents


trait CollectUnivalentsDuringFixingWithOpt
extends AbstractRPILUAlgorithm {

  protected def fixProofAndLowerUnivalents(proof: Proof[SequentProofNode], edgesToDelete: EdgesToDelete) = {

    var univalents = List[SequentProofNode]()
    val loweredPivots = MClause()

    def fixResolutionAndDeleteUnivalent(oldNode: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
      val newNode = fixProofNodes(edgesToDelete)(oldNode, fixedPremises)
      val children = proof.childrenOf(oldNode) filter { child => !edgesToDelete.isMarked(child, oldNode) }
      isLowerableUnivalent(newNode, oldNode, children, loweredPivots, edgesToDelete.markEdge) match {
        case LowerableUnivalent(_) => univalents ::= newNode ; edgesToDelete.deleteNode(oldNode)
        case _ =>
      }
      newNode
    }
    val pseudoRoot = proof.foldDown(fixResolutionAndDeleteUnivalent _)

    /* The pivot literal needed to reintroduce univalent clause's nodes can be
     * safely forgotten. The algorithm ensures the lowered pivots clause isn't
     * tautological and that all non-valent literal of a lowered node have
     * their dual in the lowered pivots clause.                              */
    univalents.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left, right)} catch {case e:Exception => left}
    }
  }

}

abstract class LowerUnivalentsOpt
extends AbstractRPILUAlgorithm with CollectUnivalentsDuringFixingWithOpt with IdempotentAlgorithm[SequentProofNode] {

  def apply(proof: Proof[SequentProofNode]) =
    Proof(fixProofAndLowerUnivalents(proof, new EdgesToDelete()))

}

object LowerUnivalentsOpt
extends LowerUnivalentsOpt



abstract class LowerUnivalentsAfterRecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals with CollectUnivalentsDuringFixing with Intersection
{

  def apply(proof: Proof[SequentProofNode]) = {
    val edgesToDelete = collectEdgesToDelete(proof)
    Proof(fixProofAndLowerUnivalents(proof, edgesToDelete))
  }

}

object LowerUnivalentsAfterRecyclePivots
extends LowerUnivalentsAfterRecyclePivots with RepeatableWhileCompressingAlgorithm[SequentProofNode]

object IdempotentLowerUnivalentsAfterRecyclePivots
extends LowerUnivalentsAfterRecyclePivots with IdempotentAlgorithm[SequentProofNode]


abstract class LowerUnivalentsAfterRecyclePivotsWithOpt
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals with CollectUnivalentsDuringFixingWithOpt with Intersection
{

  def apply(proof: Proof[SequentProofNode]) = {
    val edgesToDelete = collectEdgesToDelete(proof)
    Proof(fixProofAndLowerUnivalents(proof, edgesToDelete))
  }

}

object IdempotentLowerUnivalentsAfterRecyclePivotsOpt
extends LowerUnivalentsAfterRecyclePivotsWithOpt with IdempotentAlgorithm[SequentProofNode]

abstract class LowerUnivalentsBeforeRecyclePivots
extends AbstractThreePassLower {

  protected def collectLowerables(proof: Proof[SequentProofNode]) = {
    val loweredPivots = MClause()
    var orderedUnivalents = List[SequentProofNode]()
    val univalentsSafeLiterals = MMap[SequentProofNode, IClause]()
    val univalentsValentLiteral = MMap[SequentProofNode, IClause]()

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

  def apply(proof: Proof[SequentProofNode]) = {

    // First pass
    val (rootSafeLiterals, orderedUnivalents, univalentsSafeLiterals, univalentsValentLiteral) = collectLowerables(proof)
//    val nbUnitChildren = orderedUnivalents.foldLeft(0) { (acc,node) => acc + proof.childrenOf(node).length }
//    println(orderedUnivalents.length + " orderedUnivalents with " + nbUnitChildren + " children" )

    // Second pass
    val edgesToDelete = collectEdgesToDelete(proof, rootSafeLiterals, univalentsSafeLiterals)

    // Third pass
    if (edgesToDelete.isEmpty) proof else Proof({
      val fixMap = mapFixedProofNodes(orderedUnivalents.toSet + proof.root, edgesToDelete, proof)
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
extends LowerUnivalentsBeforeRecyclePivots with RepeatableWhileCompressingAlgorithm[SequentProofNode]

object IdempotentLowerUnivalentsBeforeRecyclePivots
extends LowerUnivalentsBeforeRecyclePivots with IdempotentAlgorithm[SequentProofNode]
