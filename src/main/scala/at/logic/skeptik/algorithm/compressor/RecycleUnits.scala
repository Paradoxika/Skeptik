package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression.E
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.SequentLike
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}

/**
 * RecycleUnits is a special case of bottom-up subsumption, which seeks to replace nodes by subsuming unit nodes.
 * The initial idea of the algorithm is, not to check for subsumption for every node with every unit clause, but to compare unit nodes to pivots.
 * If a unit clause matches a pivot, then one of the premise nodes can be changed.
 * This approach is so far not implemented, but subsumption is checked like in the bottom-up subsumption algorithm.
 * The reason for this is the way how foldDown works. It only affects the updated node for the current node itself and has no means of modifying parent nodes.
 * One could update the node to be the resolvent of the new premises, however that leaves the old premises in tact, and it will be used for premises of other nodes.
 * Moreover RecycleUnits suffers from the same copy node problems described at the bottom-up subsumption algorithm
 */

object RecycleUnits extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with fixNodes {
  
  def isUnit[P <: ProofNode[Sequent,P]](n: P) = n.conclusion.width == 1
  
  def apply(proof: Proof[SequentProofNode]) = {
    //stores the descendant unit nodes of all proof nodes
    val descUnits = new MMap[SequentProofNode,MSet[SequentProofNode]]
    //store the ancestor unit nodes of all proof nodes
    val ancUnits = new MMap[SequentProofNode,MSet[SequentProofNode]]
    //node map to do dagification on the fly to ease the copy node issue
    val nodeMap = MMap[Sequent,SequentProofNode]()
    //Set of unit nodes occuring in the proof
    val unitNodes = new MSet[SequentProofNode]
    
    def collectUnits(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      //collect seen units from children nodes
      val descChild = (new MSet[SequentProofNode] /: children)( (l1,l2) =>
        l1 union descUnits(l2)
      )
      //add unit clause to global set
      if (isUnit(node)) {
        unitNodes += node
      }
      
      //add unit clause to seen units for this node
      descUnits += (node -> (if (isUnit(node)) descChild + node else descChild))
      node
    }
    
    //collect the ancestor unit nodes for every node
    //unfortunately this has to be done beforehand and needs an extra traversal, but without this information cyclic proofs might result after replacing some node by a unit
    def getAncUnits(node: SequentProofNode, res: Seq[Unit]):Unit ={
      val ancPremises = (new MSet[SequentProofNode] /: node.premises)( (l1,l2) =>
        l1 union ancUnits(l2)
      )
      if (isUnit(node)) {
        ancPremises += node
      }
      ancUnits(node) = ancPremises
    }

    //It's a little unfortunate, that I need two pre-proccessing traversals, but both ancestor and descendant unit nodes information is crucial for correctness
    proof bottomUp collectUnits
    proof foldDown getAncUnits

    //Helper method to replace one reference to a unit node by another unit node with the same literal in all the helper maps and sets
    def replaceUnitbyUnit(oldUnit: SequentProofNode, newUnit: SequentProofNode) {
      unitNodes -= oldUnit
      unitNodes += newUnit
      //This traversal is likely to be inefficient, maybe by changing the way descendant and ancestor units information is stored this could be done more efficiently
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
    
    def replace(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      //On the fly dagification
      if (nodeMap.contains(node.conclusion)) nodeMap(node.conclusion)
      else {
        val newNode = fixNode(node,fixedPremises)
        if (!(newNode eq node) && (isUnit(newNode)) && (isUnit(node))) { //A unit node got a new reference (because its premises have been changed) and from now on this new reference should be used
          replaceUnitbyUnit(node,newNode)
        }
        if (newNode.isInstanceOf[R] || newNode.isInstanceOf[Axiom]) {
          nodeMap += (newNode.conclusion -> newNode)
        }
        if (!(newNode eq node)) { //If the node was actually fixed, then the ancestor, descendant unit node information is copied from the original node
          ancUnits(newNode) = ancUnits(node)
          descUnits(newNode) = descUnits(node)
        }
        //A unit node, which does not create a cyclic proof if replaced for this node is searched for
        unitNodes.find(u => (u.conclusion subsequentOf newNode.conclusion) && !(fixedPremises contains u) && !descUnits(newNode).contains(u) && (ancUnits(u) intersect descUnits(newNode)).isEmpty) match {
          case None => newNode
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
