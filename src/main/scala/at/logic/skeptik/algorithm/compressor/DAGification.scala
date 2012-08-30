package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

object DAGification
extends CompressorAlgorithm[SequentProofNode] with IdempotentAlgorithm[SequentProofNode] {

  // TODO: optimize to directly construct a Proof
  def apply(proof: Proof[SequentProofNode]) = {
    val nodeMap = MMap[Sequent,SequentProofNode]()
    def dagify(node: SequentProofNode, premises: Seq[SequentProofNode]) = node match {
      case _ if nodeMap.contains(node.conclusion) => nodeMap(node.conclusion)
      case Axiom(conclusion) => nodeMap.update(conclusion, node) ; node
      case CutIC(left,right,aux,_) => 
        val fixedLeft  = premises.head
        val fixedRight = premises.last
        val newNode = if ((left eq fixedLeft) && (right eq fixedRight)) node else CutIC(fixedLeft, fixedRight, _ == aux)
        nodeMap.update(newNode.conclusion, newNode)
        newNode
    }
    Proof(proof.foldDown(dagify))
  }

}

