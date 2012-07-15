package skeptik.algorithm.compressor

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

object DAGification
extends Function1[SequentProof,SequentProof] {
  def apply(proof: SequentProof) = {
    val nodeCollection = ProofNodeCollection(proof)
    val nodeMap = MMap[Sequent,SequentProof]()
    def dagify(node: SequentProof, premises: List[SequentProof]) = node match {
      case _ if nodeMap.contains(node.conclusion) => nodeMap(node.conclusion)
      case Axiom(conclusion) => nodeMap.update(conclusion, node) ; node
      case CutIC(left,right,aux,_) => 
        val fixedLeft  = premises.head
        val fixedRight = premises.last
        val newNode = if ((left eq fixedLeft) && (right eq fixedRight)) node else CutIC(fixedLeft, fixedRight, _ == aux)
        nodeMap.update(newNode.conclusion, newNode)
        newNode
    }
    nodeCollection.foldDown(dagify)
  }
}

