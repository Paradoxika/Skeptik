package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import scala.collection.mutable.{HashMap => MMap}

abstract class AbstractSubsumption 
extends (Proof[SequentProofNode] => Proof[SequentProofNode])

object ForwardSubsumption extends AbstractSubsumption {
  
  def apply(proof: Proof[SequentProofNode]) = {
    val nodeMap = new subsumeMap

    Proof(proof foldDown { (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => node match {
      case Axiom(conclusion) => nodeMap += (conclusion -> node) ; node
      case R(left, right, pivot, _) => {
        //check the visited nodes if there is a subsuming one
        val subsumer = nodeMap.getSubsumer(node.conclusion)
        
        //in case there is subsumer is that node and it can the current node can be replaced by this node
        if (subsumer != null) {
          subsumer
        }
        
        //if there is no subsumer, the proof validity of the proof structure has to be checked and possibly fixed 
        else
        {
	        val fixedLeft  = fixedPremises.head
	        val fixedRight = fixedPremises.last
	        val newNode = 
	        //nothing has changed
	        if ((left eq fixedLeft) && (right eq fixedRight)) node 
	        
	        //something is different
	        else {
	          //check which parent node still contains the pivot element
	          val leftcontained = fixedLeft.conclusion contains pivot
	          val rightcontained = fixedRight.conclusion contains pivot
	          
	          //replace the current node by the parent which does not contain the pivot
	          //currently favouring the left parent (better heuristic here?)
	          if (!leftcontained) fixedLeft
	          else if (!rightcontained) fixedRight
	          
	          //if both parents contain the pivot element -> update the current node as a resolvent of its parent nodes
	          else R(fixedLeft, fixedRight, pivot)
	        }
	        nodeMap += (newNode.conclusion -> newNode)
	        newNode
        }
      }
      case _ => node
    }})
  }
}

class subsumeMap extends MMap[Sequent,SequentProofNode]
{
  def getSubsumer(subsumed: Sequent):SequentProofNode = 
  {
    foreach( entry => if (entry._1 subsequentOf subsumed) return entry._2)
    return null;
  }
}