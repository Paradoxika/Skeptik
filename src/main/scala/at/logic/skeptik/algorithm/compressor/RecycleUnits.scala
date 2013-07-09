package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}

object RecycleUnits extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {
  
  def apply(proof: Proof[SequentProofNode]) = {
    val descUnits = new MMap[SequentProofNode,MSet[SequentProofNode]]
    val units = new MSet[SequentProofNode]
    
    
    def collectUnits(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      //collect seen units from children nodes
      val descChild = children.foldLeft(new MSet[SequentProofNode])((l1,l2) =>
          descUnits.get(l2) match {
            case Some(u) => l1 union u
            case None => l1
          }
      )
      //add unit clause to global set
      if (node.conclusion.size == 2) units += node
      
      //add unit clause to seen units for this node
      descUnits += (node -> (if (node.conclusion.size == 2) descChild + node else descChild))
      node
    }

    proof.bottomUp(collectUnits)
       
    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => node match {
      case R(left, right, pivot, _) => {
        val fixedLeft  = fixedPremises.head
		val fixedRight = fixedPremises.last
        units.find(u => {
          val notancestor = descUnits.get(node).forall(units => !units.contains(u))
          notancestor && u.conclusion.contains(pivot) }) match {
          case None => {
		    if ((left eq fixedLeft) && (right eq fixedRight)) node 
		    else R(fixedLeft,fixedRight,pivot,true)
          }
          case Some(u) => {
            if (u.conclusion.ant.contains(pivot)) R(u,fixedRight,pivot)
            else R(fixedLeft,u,pivot)
          }
        }
        
      }
      case _ => node
    })})
  }
}
