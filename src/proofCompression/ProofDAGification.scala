/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import proofCompression.Utilities._
import scala.collection.mutable._

object ProofDAGification {
  def replace(replaced: ResolutionProof, replacer: ResolutionProof) = {
    for (c <- replaced.children) {
      replacer.children = c::replacer.children
      if (c.left == replaced) c.left = replacer
      else c.right = replacer
    }
    replaced.children = Nil
  }

  def DAGify(proof: ResolutionProof) = {
    def DAGifyRec(p: ResolutionProof, visitedProofs: HashSet[ResolutionProof], map: HashMap[scala.collection.immutable.Set[Literal],ResolutionProof]): Unit = {
      if (!visitedProofs.contains(p)) {
        if (p.isInstanceOf[Resolvent]) {
          DAGifyRec(p.asInstanceOf[Resolvent].left, visitedProofs, map)
          DAGifyRec(p.asInstanceOf[Resolvent].right, visitedProofs, map)
        }
        map.get(p.clause.toSet[Literal]) match {
          case None => map += (p.clause.toSet[Literal] -> p)
          case Some(otherProof) => {
            if (proofLength(otherProof) < proofLength(p)) {
              replace(p, otherProof)
            }
            else {
              replace(otherProof, p)
              map -= otherProof.clause.toSet[Literal]
              map += (p.clause.toSet[Literal] -> p)
            }
          }
        }

        visitedProofs += p
      }
    }
    DAGifyRec(proof, new HashSet[ResolutionProof], new HashMap[scala.collection.immutable.Set[Literal],ResolutionProof])
  }
}
