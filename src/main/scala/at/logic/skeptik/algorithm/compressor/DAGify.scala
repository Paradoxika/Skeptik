package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.{Axiom, R}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}


object DAGify 
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {
  def apply(proof: Proof[SequentProofNode]) = {
    val nodeMap = MMap[Sequent,SequentProofNode]()

    Proof(proof foldDown { (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => node match {
      case _ if nodeMap.contains(node.conclusion) => nodeMap(node.conclusion)
      case Axiom(conclusion) => nodeMap += (conclusion -> node) ; node
      case R(left, right, pivot, _) => {
        val fixedLeft  = fixedPremises.head
        val fixedRight = fixedPremises.last
        val newNode = if ((left eq fixedLeft) && (right eq fixedRight)) node 
                      else R(fixedLeft, fixedRight, pivot)
        nodeMap += (newNode.conclusion -> newNode)
        newNode
      }
      case _ => node
    }})
  }
}

