package at.logic.skeptik.algorithm.compressor.subsumption

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}
import at.logic.skeptik.algorithm.compressor.fixNodes

/**
 * RecycleUnits is a special case of bottom-up subsumption, which replaces nodes by subsuming unit nodes.
 * 
 * The initial idea of the algorithm is not to check for subsumption for every node with every unit clause, 
 * but to compare unit nodes to pivots.
 * If a unit clause matches a pivot, then one of the premise nodes can be changed.
 * This approach is so far not implemented, 
 * but subsumption is checked like in the bottom-up subsumption algorithm.
 * The reason for this is the way foldDown works. 
 * Using an updated premise only affects the node which is currently being processed
 * and has no effects on the premise itself.
 * If the original premise has another child, it remains in the proof as the premise of that child.
 * Moreover RecycleUnits suffers from the same copy node problems described at the bottom-up subsumption algorithm.
 */

object RecycleUnits extends (Proof[N] => Proof[N]) with fixNodes {
  
  def isUnit(n: N) = n.conclusion.width == 1
  
  def apply(proof: Proof[N]) = {
    //stores the descendant unit nodes of all proof nodes
    val descUnits = new MMap[N,MSet[N]]
    //store the ancestor unit nodes of all proof nodes
    val ancUnits = new MMap[N,MSet[N]]
    //node map to do dagification on the fly to ease the copy node issue
    val nodeMap = MMap[Sequent,N]()
    //Set of unit nodes occurring in the proof
    val unitNodes = new MSet[N]
    
    def collectUnits(node: N, children: Seq[N]):N = {
      //collect seen units from children nodes
      val descChild = (children foldLeft MSet[N]())( (l1,l2) =>
        l1 union descUnits(l2)
      )
      //add unit clause to global set
      if (isUnit(node)) {
        unitNodes += node
      }
      
      //add unit clause to seen units for this node
      descUnits += (node -> (
          if (isUnit(node)) 
            descChild + node 
          else 
            descChild
          ))
      node
    }
    
    /**
     * Collects the ancestor unit nodes for every node.
     * Unfortunately this has to be done beforehand and needs an extra traversal, 
     * but without this information cyclic proofs might result after replacing some node by a unit.
     */
    def getAncUnits(node: N, res: Seq[Unit]):Unit ={
      val ancPremises = (new MSet[N] /: node.premises)( (l1,l2) =>
        l1 union ancUnits(l2)
      )
      if (isUnit(node)) {
        ancPremises += node
      }
      ancUnits(node) = ancPremises
    }

    proof bottomUp collectUnits
    proof foldDown getAncUnits

    /**
     * Helper method to replace one reference to a unit node by another unit node with the same literal
     * in all the information maps and sets
     */
    def replaceUnitbyUnit(oldUnit: N, newUnit: N) {
      unitNodes -= oldUnit
      unitNodes += newUnit
      //This traversal is likely to be inefficient
      //by changing the way descendant and ancestor units information is stored 
      //this could possibly be done more efficiently
      descUnits.foreach(dU => {
        if (dU._2 contains oldUnit) {
          dU._2 -= oldUnit
          dU._2 += newUnit
        }
      })
      ancUnits.foreach(dU => {
        if (dU._2 contains oldUnit) {
          dU._2 -= oldUnit
          dU._2 += newUnit
        }
      })
    }
    
    def replace(node: N, fixedPremises: Seq[N]):N = {
      //On the fly dagification
      if (nodeMap.contains(node.conclusion)) nodeMap(node.conclusion)
      else {
        val newNode = fixNode(node,fixedPremises)
        //A unit node got a new reference (because its premises have been changed)
        //and from now on this new reference should be used
        //therefore the old one has to be replaced by the new one in the information maps and sets
        if (!(newNode eq node) && (isUnit(newNode)) && (isUnit(node))) { 
          replaceUnitbyUnit(node,newNode)
        }
        //If the node was fixed to a new node, 
        //ancestor and descendant unit node information is copied from the original node
        if (!(newNode eq node)) { 
          ancUnits(newNode) = ancUnits(node)
          descUnits(newNode) = descUnits(node)
        }
        //A unit node, which does not create a cyclic proof if replaced for this node is searched for
        val rep = unitNodes.find(u => 
          (  (u.conclusion subsequentOf newNode.conclusion) 
          && !(fixedPremises contains u) 
          && !descUnits(newNode).contains(u) 
          && (ancUnits(u) intersect descUnits(newNode)).isEmpty)
          ) 
        rep match {
          case None => {
            nodeMap += (newNode.conclusion -> newNode)
            newNode
          }
          case Some(u) => {
            u
          }
        }
      }
    }
    
    val out = Proof(proof foldDown replace)
    
    //Since there can be negative compression, only shorter proofs are accepted
    if (out.size < proof.size) out else proof
  }
}
