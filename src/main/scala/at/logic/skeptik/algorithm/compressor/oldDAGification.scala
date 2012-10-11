package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.oldResolution._
import at.logic.skeptik.proof.oldResolution.typeAliases._
import collection._

object oldDAGification {
  def DAGify(proof: ProofNode, measure: ProofNode => Int): ProofNode = {
    val visitedProofNodes = new mutable.HashSet[ProofNode]
    val map = new mutable.HashMap[Clause,ProofNode]
    def rec(p: ProofNode): Unit = {
      if (!visitedProofNodes.contains(p)) {
        if (p.isInstanceOf[Resolvent]) {
          rec(p.asInstanceOf[Resolvent].left)
          rec(p.asInstanceOf[Resolvent].right)
        }
        map.get(p.clause) match {
          case None => map += (p.clause -> p)
          case Some(otherProofNode) => {
            if (measure(otherProofNode) < measure(p)) {
              otherProofNode replaces p
            }
            else {
              p replaces otherProofNode   // OldToDo: I changed the "replaces" method. Hence this line might not work anymore.
              map -= otherProofNode.clause
              map += (p.clause -> p)
            }
          }
        }
        visitedProofNodes += p
      }
    }
    rec(proof)
    proof
  }
}
