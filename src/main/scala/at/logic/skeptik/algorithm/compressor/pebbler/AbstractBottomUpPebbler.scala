package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}

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
   
  def findProof(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], initNodes: MSet[N]): Proof[N] = {
    var permutation: Seq[N] = Seq[N]()
    val visited = MSet[N]()
    
    /**
     * Computes the final permutation by recursively visiting the premises of nodes
     * in the order corresponding to the used heuristic
     * visited nodes are stored, so no node is visited twice
     */
    def visit(p: N): Unit = if (!visited(p)) {
      visited += p
      var premises = p.premises
      while (!premises.isEmpty) {
        val next = premises.max(usedOrder(proof,nodeInfos))
        premises = premises.diff(Seq(next))
        visit(next)
      }
      permutation = permutation :+ p
    }
    visit(proof.root)
    new Proof(proof.root, permutation.reverse.toIndexedSeq)
  }
}
