/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import scala.collection._

object ProofFixing {
  def fix(p:Proof): Proof = {fixRec(p, new mutable.HashSet[Proof]); p}
  def fix(proofs:List[Proof]): List[Proof] = {
    val visitedProofs = new mutable.HashSet[Proof]
    for (p <- proofs) fixRec(p,visitedProofs)
    proofs
  }

  private def fixRec(proof:Proof, visitedProofs: mutable.HashSet[Proof]) : Unit = {
    if (!visitedProofs.contains(proof)) {
      visitedProofs += proof
      proof match {
        case Input(c) => return
        case n : Resolvent => {
          fixRec(n.left, visitedProofs)
          fixRec(n.right, visitedProofs)
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
}
