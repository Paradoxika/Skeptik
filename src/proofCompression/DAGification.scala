/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import proofCompression.Utilities._
import scala.collection._

object DAGification {
  def DAGify(proof: Proof, measure: Proof => Int): Proof = {
    val visitedProofs = new mutable.HashSet[Proof]
    val map = new mutable.HashMap[Clause,Proof]
    def rec(p: Proof): Unit = {
      if (!visitedProofs.contains(p)) {
        if (p.isInstanceOf[Resolvent]) {
          rec(p.asInstanceOf[Resolvent].left)
          rec(p.asInstanceOf[Resolvent].right)
        }
        map.get(p.clause) match {
          case None => map += (p.clause -> p)
          case Some(otherProof) => {
            if (measure(otherProof) < measure(p)) {
              otherProof replaces p
            }
            else {
              p replaces otherProof   // ToDo: I changed the "replaces" method. Hence this line might not work anymore.
              map -= otherProof.clause
              map += (p.clause -> p)
            }
          }
        }
        visitedProofs += p
      }
    }
    rec(proof)
    proof
  }
}
