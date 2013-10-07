package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}

/**
 * Top down pebblers traverse the proof from leaves to the root and pebble nodes
 * using a specific heuristic in form of a node ordering.
 * 
 * By pebbling nodes, other nodes are made available for pebbling 
 * while initially only nodes without premises are available.
 * This is done until no more nodes are available for pebbling, i.e. the root node is pebbled.
 * Top-down pebbling directly corresponds to playing the Black Pebbling Game
 * */

abstract class AbstractTopDownPebbler extends AbstractPebbler  {
  def findProof(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], initNodes: MSet[N]): Proof[N] = {
    //Pebbled nodes go into this Seq
    var permutation:Seq[N] = Seq[N]()
    
    val canBePebbled:MSet[N] = initNodes
    
    proof.nodes.foreach(n => {
      if (n.premises.isEmpty) canBePebbled += n
    })
    
    while(!canBePebbled.isEmpty) {
      //Choose the next node as the maximum w.r.t. the used heuristic of pebbleable nodes
      val next = canBePebbled.max(usedOrder(proof,nodeInfos))
      
      permutation = permutation :+ next
      canBePebbled -= next
      
      //Update the relevant nodeInfo objects
      next.premises.foreach(pr => {
        if (nodeInfos.isDefinedAt(pr)) {
          val cNP = nodeInfos(pr).childrenNotPebbled - 1
          //This premise can be unpebbled.
          if (cNP == 1) {
            nodeInfos -= pr
          }
          else {
            nodeInfos(pr).childrenNotPebbled = cNP
          }
        }
      })
      //calculate an upper bound for the number of pebbles used for this node as 
      //the sum of the upper bounds of all premises plus 1
      nodeInfos(next).usesPebbles = (next.premises foldLeft 1) ((A,B) => 
        A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
      
      //visit all children of the current node and decrement their waitsForPremises number by 1
      //if this number was 1 before for a children c, then c can be made available for pebbling
      proof.childrenOf(next).foreach(c => {
        val wF = nodeInfos(c).waitsForPremises
        nodeInfos(c).waitsForPremises = wF - 1
        if (wF == 1) {
          canBePebbled += c
        }
      })
      
    }
    new Proof(proof.root, permutation.reverse.toIndexedSeq)
  }
}
