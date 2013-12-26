package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}
import scala.collection.mutable.ArrayBuffer

/**
 * Bottom up pebblers find a topological order while traversing the proof from root to leafs.
 * 
 * At each node n its premises are visited recursively before n is processed.
 * It is decided heuristically in what order the premises are visited.
 * So far these pebblers have behaved better in reducing the space measure than top down pebblers.
 * I think this is the case, because "far away" new branches are not touched before old ones are finished,
 * which is often the case for (greedy) top-down pebblers, but not for bottom-up pebblers.
 */

abstract class AbstractBottomUpPebbler extends AbstractPebbler  {
  
  def findFirstOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = usedOrder(proof, nodeInfos)
  
  def findProof(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], reverseNode: Option[N]): Proof[N] = {
//    println(nodeInfos.size)
//    var permutation: Seq[N] = Seq[N]()
    val permutation = new ArrayBuffer[N]()
    val visited = MSet[N]()
    
    var currentOrder = findFirstOrder(proof, nodeInfos)
    
    /**
     * Computes the final permutation by recursively visiting the premises of nodes
     * in the order corresponding to the used heuristic
     * visited nodes are stored, so no node is visited twice
     */
    def visit(p: N): Unit = if (!visited(p)) {
      visited += p
      if (!nodeInfos.isDefinedAt(p)) {
        nodeInfos += (p -> new NodeInfo)
      }
      var premises = p.premises
      while (!premises.isEmpty) {
        val next = 
          if (reverseNode.exists(_ eq p)) premises.min(usedOrder(proof,nodeInfos))
          else premises.max(currentOrder)
        premises = premises.diff(Seq(next))
        visit(next)
      }
      currentOrder = usedOrder(proof, nodeInfos)
//      permutation = permutation :+ p
      permutation += p
      nodeInfos.update(p, nodeInfos.getOrElse(p, new NodeInfo).changeWasPebbled(permutation.size))
      nodeInfos.update(p, nodeInfos.getOrElse(p, new NodeInfo).changeUsesPebbles(1))
      //unpebble premises
      p.premises.foreach(pr => {
        if (proof.childrenOf(pr).forall(ch => nodeInfos.getOrElse(pr, new NodeInfo).usesPebbles != 0))
          nodeInfos.update(pr, nodeInfos.getOrElse(pr, new NodeInfo).changeUsesPebbles(0))
      })
//      print(nodeInfos(p).index + ", ")
    }
    visit(proof.root)
//    println()
//    nodeInfos.clear
    new Proof(proof.root, permutation.reverse.toIndexedSeq)
//    proof
  }
}