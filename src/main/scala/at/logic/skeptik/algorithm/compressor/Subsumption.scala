package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}

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

object BWS extends AbstractSubsumption {

  def apply(proof: Proof[SequentProofNode]) = {
    val nodeMap = new MMap[Sequent,SequentProofNode]
    val antNodes = new MMap[SequentProofNode,MSet[SequentProofNode]]
    val replaceNodes = new MMap[SequentProofNode,SequentProofNode]
    
    def collect(node: SequentProofNode, results: Seq[Unit]):Unit = {
      val premises = node.premises
      val antPremises = (new MSet[SequentProofNode] /: premises)( (l1,l2) =>
        l1 union antNodes(l2)
      )
      antNodes += (node -> (antPremises + node))
      
      val subsumed = nodeMap.find( A => (node.conclusion subsequentOf A._1) && !(antNodes(node) contains A._2))
      val subsMap = subsumed.map(a => a._2)
      subsMap.foreach(u => {
        replaceNodes.get(u) match {
          case Some(v) => if (v.conclusion.size > node.conclusion.size) replaceNodes(u) = node
          case None => replaceNodes += (u -> node)
        }})

      node match {
        case Axiom(conclusion) => nodeMap += (conclusion -> node)
        case R(_,_,_,_) => nodeMap += (node.conclusion -> node)
        case _ => Unit
      }
    }
    
    
    proof.foldDown(collect)
    
    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
    	
      replaceNodes.getOrElse(node,{
        node match {
          case R(left, right, pivot, _) => {
            val fixedLeft  = fixedPremises.head
	        val fixedRight = fixedPremises.last
	        val newNode = 
	          if ((left eq fixedLeft) && (right eq fixedRight)) node 
	          else R(fixedLeft,fixedRight,pivot,true)
	          newNode
            }
          case _ => node
        }
      })
    })})
  }
}