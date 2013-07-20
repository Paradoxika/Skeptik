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

abstract class BWS extends AbstractSubsumption {
  val nodeMap = new MMap[Sequent,SequentProofNode]
  val replaceNodes = new MMap[SequentProofNode,SequentProofNode]
  
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean
  
  def collect(node: SequentProofNode, results: Seq[Unit]):Unit = {
    val subsumed = nodeMap.find( A => (notAncestor(node,A._2) && (node.conclusion subsequentOf A._1)))
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
  
  def apply(proof: Proof[SequentProofNode]) = {
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

object BWSt extends BWS {
  val ancestors = new MMap[SequentProofNode,MSet[SequentProofNode]]
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean = {
    !(ancestors.getOrElse(node, computeAncestors(node)) contains ancestor)
  }
  def computeAncestors(node: SequentProofNode):MSet[SequentProofNode] = {
    val premises = node.premises
    val ancPremises = (new MSet[SequentProofNode] /: premises){ (l1,l2) =>
      l1 union ancestors.getOrElse(l2, {new MSet[SequentProofNode] + l2})
    }
    ancestors += (node -> (ancPremises + node))
    ancestors(node)
  }
}

object BWSm extends BWS {
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean = {
    !(node existsAmongAncestors {_ eq ancestor})
  }
}
