package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}
import at.logic.skeptik.proof.measure

/**
 * Abstract pebbling class, both for top-down and bottom-up pebblers
 * 
 * Pebblers aim to reduce the space measure,
 * i.e. the number of nodes that have to be kept in memory at once.
 * This is done by finding a topological ordering,
 * which is an indexing of the nodes, such that for every node 
 * all its premises have a lower index than the node itself.
 * This topological order can be used to rearrange the proof
 * and (hopefully) reduce the space measure.
 */
abstract class AbstractPebbler extends (Proof[N] => Proof[N])  {
  
  /** Represents the used heuristic */
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N]
  
  /** This is where top-down and bottom-up differ */
  def findProof(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], initNodes: MSet[N]): Proof[N] = {
    findProof(proof,nodeInfos,initNodes,None)
  }
  
  def findProof(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], initNodes: MSet[N], reverseNode: Option[N]): Proof[N]
  
  def apply(proof: Proof[N]): Proof[N] = {
    val (nodeInfos,initNodes) = initInfos(proof)
    findProof(proof,nodeInfos,initNodes)
  }
  
  def initInfos(proof: Proof[N]) = {
    val nodeInfos:MMap[N,NodeInfo] = MMap[N,NodeInfo]()
    //Set of nodes that can be pebbled initially, i.e. the axioms
    val initNodes: MSet[N] = MSet[N]()
    var counter = 0
    val proofSize = proof.size
    /**
     * Traverses the proof bottom up and create a NodeInfo object for each node
     * Adds all nodes without premises to the set of initially pebbleable nodes
     */
    def gather(node: N, children: Seq[N]):N = {
      if (node.premises.isEmpty) initNodes += node
      val impact = 
        if (children.size > 0) 
          children.map(c => nodeInfos(c).impact / c.premises.size).min
        else 1
      val depth = 
        if (children.size > 0) 
          children.map(c => nodeInfos(c).depth).min + 1 
        else 0
      val inSubProof = 
        if (children.size > 0)
          children.foldLeft(1)((A,B) => A + nodeInfos(B).inSubProof)
        else 1
      val nI = new NodeInfo(proofSize-counter, depth, children.size, inSubProof, 0, node.premises.size, 0, children.size, 0, false, impact)
//      println("node# :" + (proofSize-counter) + " has impact: " + impact + " and depth: " + depth + " inSubProofs: " + inSubProof)
      nodeInfos += (node -> nI)
      children.lastOption.foreach(l => {
        val current = nodeInfos(l)
        nodeInfos(l) = current.changeLastChildOf(current.lastChildOf + 1)
      })
      counter = counter + 1
      node
    }
    proof bottomUp gather
    
    (nodeInfos,initNodes)
  }
  
  def climbOnce(proof: Proof[N]): Proof[N] = {
    val (nodeInfos,initNodes) = initInfos(proof)
    val initProof = findProof(proof,nodeInfos,initNodes)
    var bestProof = initProof
    var bestM = measure(bestProof)("space")
//    var bestNodeInfos = nodeInfos
    nodeInfos.foreach(nodeInfo => {
      val currentNodeInfos = nodeInfos.clone
      val currentProof = WasPebbledPebbler.findProof(initProof,currentNodeInfos,initNodes,Some(nodeInfo._1))
      val currentM = measure(currentProof)("space")
      if (currentM < bestM) {
        bestProof = currentProof
        bestM = currentM
      }
    })
    bestProof
  }
}