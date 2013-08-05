package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression.E
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.SequentLike
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}

object RecycleUnits extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with fixNodes {
  
  def isUnit[P <: ProofNode[Sequent,P]](n: P) = n.conclusion.width == 1
  
  def apply(proof: Proof[SequentProofNode]) = {
    //stores the unit descendend unit nodes of all proof nodes
    val descUnits = new MMap[SequentProofNode,MSet[SequentProofNode]]
    //stores occuring unit nodes in the proof for pivot elements
    val units = new MMap[E,MSet[SequentProofNode]]
    
    
    
    def collectUnits(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      //collect seen units from children nodes
      val descChild = (new MSet[SequentProofNode] /: children)( (l1,l2) =>
        l1 union descUnits(l2)
      )
      //add unit clause to global set
      if (isUnit(node)) {
        node.conclusion.ant.foreach(l => units(l) = units.getOrElse(l, new MSet[SequentProofNode]) += node )
        node.conclusion.suc.foreach(l => units(l) = units.getOrElse(l, new MSet[SequentProofNode]) += node )
      }
      
      //add unit clause to seen units for this node
      descUnits += (node -> (if (isUnit(node)) descChild + node else descChild))
      node
    }

    proof.bottomUp(collectUnits)
       
    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => node match {
    case R(left, right, pivot, _) => {
      val fixedLeft  = fixedPremises.head
  		val fixedRight = fixedPremises.last
  		//find unit nodes with the current pivot element which are not ancestors of the current node
  		units.getOrElse(pivot,new MSet[SequentProofNode]).find(u => ! descUnits(node).contains(u)) match {
        //in case there are no such units -> update the node if needed
        case None => {
          fixNode(node,pivot,left,right,fixedLeft,fixedRight)
        }
        //there is a not ancestor unit in the proof using the current pivot
        case Some(u) => {
          //println(u.conclusion + " contains " + pivot + " suc c: " + u.conclusion.suc.contains(pivot))
          //pivot is negative
          if (u.conclusion.suc.contains(pivot)) fixNode(node,pivot,left,right,u,fixedRight)
          //pivot is positive
          else fixNode(node,pivot,left,right,fixedLeft,u)
        }
      }}
      case _ => node
    })})
  }
}
