package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression.E
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.SequentLike
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}

import scala.collection.mutable.{HashSet, HashMap}

/**
  * Just like {@link at.logic.skeptik.algorithm.compressor.RecycleUnits}, but
  * with top-down traversal instead of bottom-up.
  */
object TopDownRecycleUnits extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {

  def isUnit[P <: ProofNode[Sequent, P]](n: P) = n.conclusion.width == 1

  def apply(proof: Proof[SequentProofNode]) = {
    val ancestors = new MMap[SequentProofNode, MSet[SequentProofNode]]
    val units = new MMap[E, MSet[SequentProofNode]]

    def collectUnits(node: SequentProofNode, children: Seq[SequentProofNode]): SequentProofNode = {
      if (isUnit(node)) {
        node.conclusion.ant.foreach(l => units(l) = units.getOrElse(l, new MSet[SequentProofNode]) += node)
        node.conclusion.suc.foreach(l => units(l) = units.getOrElse(l, new MSet[SequentProofNode]) += node)
      }

      ancestors(node) = ancestors.getOrElse(node, new MSet[SequentProofNode]) ++= node.premises

      node
    }

    proof.topDown(collectUnits)

    Proof(proof foldDown {
      ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => node match {
        case R(left, right, pivot, _) => {
          val fixedLeft = fixedPremises.head
          val fixedRight = fixedPremises.last
          units.getOrElse(pivot, new MSet[SequentProofNode]).find(u => !ancestors(u).contains(node)) match {
            case None => {
              if ((left eq fixedLeft) && (right eq fixedRight)) node
              else R(fixedLeft, fixedRight, pivot, true)
            }
            case Some(u) => {
              if (u.conclusion.suc.contains(pivot)) R(u, fixedRight, pivot, true)
              else R(fixedLeft, u, pivot, true)
            }
          }
        }
        case _ => node
      })
    })
  }
}