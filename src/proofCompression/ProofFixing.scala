/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import scala.collection._

object ProofFixing {
  def fixProof(proof:Proof) = {
    val visitedProofs = new mutable.HashSet[Proof]
    def rec(proof:Proof) : Unit = {
      if (!visitedProofs.contains(proof)) {
        visitedProofs += proof
        proof match {
          case Input(c) => return
          case n : Resolvent => {
            rec(n.left)
            rec(n.right)
            if (n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) {
              n.update
            }
            else {
              val survivingParent : Proof =
                if (n.left == deletedSubProof) n.right
                else if (n.right == deletedSubProof) n.left
                else if (n.left.clause.contains(n.pivot._1) && !n.right.clause.contains(n.pivot._2)) n.right
                else if (!n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) n.left
                else {
                  if (n.left.length < n.right.length) n.left
                  else n.right
                }
              n.left.children -= n
              n.right.children -= n
              for (child <- n.children) {
                if (child.left == n) child.left = survivingParent
                else child.right = survivingParent
                survivingParent.children = child::survivingParent.children
              }
            }
          }
        }
      }
    }
    rec(proof)
  }
}
