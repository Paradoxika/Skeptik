package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}

abstract class AbstractSubsumption 
extends (Proof[SequentProofNode] => Proof[SequentProofNode])

object FWS extends AbstractSubsumption {
  
  def apply(proof: Proof[SequentProofNode]) = {
    val nodeMap = new MMap[Sequent,SequentProofNode]

    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
        val subsumer = nodeMap.find( A => A._1.subsequentOf(node.conclusion))
        val subsMap = subsumer.map(a => a._2)
        
        subsMap.getOrElse({
          node match {
            case Axiom(conclusion) => nodeMap += (conclusion -> node) ; node
            case R(left, right, pivot, _) => {
	          val fixedLeft  = fixedPremises.head
		      val fixedRight = fixedPremises.last
		      val newNode = 
		        if ((left eq fixedLeft) && (right eq fixedRight)) node 
		        else R(fixedLeft,fixedRight,pivot,true)
		        nodeMap += (newNode.conclusion -> newNode)
		        newNode
	        }
            case _ => node
          }
        })
      })
    })
  }
}