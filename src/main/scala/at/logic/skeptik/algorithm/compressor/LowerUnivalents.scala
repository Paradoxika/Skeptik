package at.logic.skeptik.algorithm.compressor

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

  // TODO: rename private functions

  object isLowerableUnivalent
  {
    def apply(newNode: SequentProofNode, oldNode: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause,
              delete: (SequentProofNode,SequentProofNode) => Unit = (_:SequentProofNode,_:SequentProofNode) => Unit ):Option[Either[E,E]] = {
//      print("[" + oldNode.conclusion + "] ")
      val literals = cleanUpActiveLiterals(newNode, oldNode, children, loweredPivots, delete)
      (literals.ant.size, literals.suc.size) match {
        case (1,0) => isTheOnlyValentLiteral(Left(literals.ant.head),  newNode, loweredPivots)
        case (0,1) => isTheOnlyValentLiteral(Right(literals.suc.head), newNode, loweredPivots)
        case _ => // println(newNode.conclusion + " no valent")
          None
      }
    }

    def apply(node: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause):Option[Either[E,E]] = {
      val literals = searchValentLiteral(node, children, loweredPivots)
      if (literals.isEmpty) None else isTheOnlyValentLiteral(literals.get, node, loweredPivots)
    }

    private def cleanUpActiveLiterals(newNode:SequentProofNode, oldNode: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause,
                                                 delete: (SequentProofNode,SequentProofNode) => Unit) = {
      val result = MClause()
      children.foreach { (child) =>
          child match {
          case CutIC(left, right, aux, _) if left  == oldNode =>
            if (loweredPivots.suc contains aux) delete(child,left)
            else if ((!(loweredPivots.ant contains aux)) && (newNode.conclusion.suc contains aux)) result += aux
          case CutIC(left, right, aux, _) if right == oldNode =>
            if (loweredPivots.ant contains aux) delete(child,right)
            else if ((!(loweredPivots.suc contains aux)) && (newNode.conclusion.ant contains aux)) aux =+: result
          case _ =>
          }
      }
      result
    }


    private def searchValentLiteral(node: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause) = {
      val it = children.iterator
      var result:Option[Either[E,E]] = None

      // Search first valent literal
      while (it.hasNext && result.isEmpty)
        it.next match {
          case CutIC(left,  _, aux, _) if (left  == node) && (!(loweredPivots.suc contains aux)) => result = Some(Right(aux))
          case CutIC(_, right, aux, _) if (right == node) && (!(loweredPivots.ant contains aux)) => result = Some(Left (aux))
          case _ =>
        }

      // Ensure it's the only one
      while (it.hasNext && !result.isEmpty)
        it.next match {
          case CutIC(left,  _, aux, _) if (left  == node) && (!(loweredPivots.suc contains aux)) && (Right(aux) != result.get) => result = None
          case CutIC(_, right, aux, _) if (right == node) && (!(loweredPivots.ant contains aux)) && (Left (aux) != result.get) => result = None
          case _ =>
        }

      result
    }

    private def isTheOnlyValentLiteral(remainingLiteral: Either[E,E], node: SequentProofNode, loweredPivots: MClause) = {
      var foundValent = false
      val searchValent = (valent: E, lowered: collection.Set[E]) => (lit: E) => {
        if (lit == valent) { foundValent = true ; true }
        else (lowered contains lit)
      }
      val (searchAnt, searchSuc) = remainingLiteral match {
        case Left (v) => (searchValent(v, loweredPivots.suc), loweredPivots.ant.contains _)
        case Right(v) => (loweredPivots.suc.contains _, searchValent(v, loweredPivots.ant))
      }

      if (node.conclusion.ant.forall(searchAnt) && node.conclusion.suc.forall(searchSuc) && foundValent) {
        remainingLiteral match {
          case Left (v) => v =+: loweredPivots
          case Right(v) => loweredPivots += v
        }
        // println(node.conclusion + " lowered");
        Some(remainingLiteral)
      } else {
        // println(node.conclusion + " not included in Delta");
        None
      }
    }


// The following is an alternative implementation.
// Currently it's faster but achieve worse compression ratio on some proofs (QF_RDL/skdmxa2/skdmxa-3x3-5.base.cvc.smt2).
/*
    def applyNew(newNode: SequentProofNode, oldNode: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause,
              delete: (SequentProofNode,SequentProofNode) => Unit = (_:SequentProofNode,_:SequentProofNode) => Unit ):Option[Either[E,E]] = {
//      print("[" + oldNode.conclusion + "] ")
      if (children.isEmpty) { return None }
      cleanUpActiveLiteralsNew(oldNode, children, loweredPivots, delete) match {
        case Some(lit) => isTheOnlyValentLiteral(lit,  newNode, loweredPivots)
        case _ => // println(newNode.conclusion + " no valent")
          None
      }
    }

    private def cleanUpActiveLiteralsNew(oldNode: SequentProofNode, children: Seq[SequentProofNode], loweredPivots: MClause,
                                                 delete: (SequentProofNode,SequentProofNode) => Unit) = {
      var result:Option[Either[E,E]] = None
      val it = children.iterator

      def loop(guard: () => Boolean, valentAction: (Either[E,E]) => Unit = (_:Either[E,E]) => Unit) = {
        if (it.hasNext) do {
          it.next match {
            case child @ CutIC(left, right, aux, _) if left  == oldNode =>
              if (loweredPivots.suc contains aux) {
                delete(child,left) ; result = None
              }
              else valentAction(Right(aux))

            case child @ CutIC(left, right, aux, _) if right == oldNode =>
              if (loweredPivots.ant contains aux) {
                delete(child,right) ; result = None
              }
              else valentAction(Left(aux))
            case _ =>
          }
        } while (it.hasNext && guard())
      }

      loop({() => false}, { (lit:Either[E,E]) => lit match {
        case Left (l) if !(loweredPivots.suc contains l) => result = Some(lit)
        case Right(l) if !(loweredPivots.ant contains l) => result = Some(lit)
        case _ =>
        }})
      if (!result.isEmpty) loop({() => !result.isEmpty}, { (lit:Either[E,E]) => if (lit != result.get) result = None})
      loop({() => true})
      result
    }
*/

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
      isLowerableUnivalent(newNode, oldNode, children, loweredPivots, edgesToDelete.markEdge) match {
        case Some(_) => univalents ::= newNode ; edgesToDelete.deleteNode(oldNode)
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


abstract class LowerUnivalentsAfterRecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals with CollectUnivalentsDuringFixing with Intersection
{

  def apply(proof: Proof[SequentProofNode]) = {
    val edgesToDelete = collectEdgesToDelete(proof)
    Proof(fixProofAndLowerUnivalents(proof, edgesToDelete))
  }

}

object IdempotentLowerUnivalentsAfterRecyclePivots
extends LowerUnivalentsAfterRecyclePivots with IdempotentAlgorithm[SequentProofNode]

// Flu

abstract class LowerUnivalentsBeforeRecyclePivots
extends AbstractThreePassLower {

  protected def collectLowerables(proof: Proof[SequentProofNode]) = {
    val loweredPivots = MClause()
    var orderedUnivalents = List[SequentProofNode]()
    val univalentsSafeLiterals = MMap[SequentProofNode, IClause]()
    val univalentsValentLiteral = MMap[SequentProofNode, Either[E,E]]()

    val rootSafeLiterals = proof.foldRight (IClause()) { (node, safeLiterals) =>
      isLowerableUnivalent(node, proof.childrenOf(node), loweredPivots) match {
        case Some(v @ Left(l))  =>
          orderedUnivalents ::= node
          univalentsValentLiteral.update(node, v)
          univalentsSafeLiterals.update(node, l +: safeLiterals)
          safeLiterals + l
        case Some(v @ Right(l)) =>
          orderedUnivalents ::= node
          univalentsValentLiteral.update(node, v)
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
        univalentsValentLiteral(univalent) match {
          case Left(l) =>
            CutIC(root, fixMap(univalent), _ == l, true)
          case Right(l) =>
            CutIC(fixMap(univalent), root, _ == l, true)
          }
      }
    })
  }

}

object LowerUnivalentsBeforeRecyclePivots
extends LowerUnivalentsBeforeRecyclePivots with RepeatableWhileCompressingAlgorithm[SequentProofNode]

object IdempotentLowerUnivalentsBeforeRecyclePivots
extends LowerUnivalentsBeforeRecyclePivots with IdempotentAlgorithm[SequentProofNode]
