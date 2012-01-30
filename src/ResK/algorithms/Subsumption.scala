/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ResK.algorithms

import ResK.calculi.resolution._
import ResK.utilities.Utilities._
import scala.collection._

object Subsumption {
//  def replaceSubsumedSubproofsVariant1(proof: Proof, measure: Proof => Int): Proof = {
//    val visitedProofs = new mutable.HashSet[Proof]
//    val subProofs = proof.getAllSubproofs(p => p.clause.size)
//
//    def rec(l: List[Proof]) : Unit = l match {
//      case Nil =>
//      case h::t => {
//          val tr = rec(t)
//          def checkAndReplaceSubsumed(possiblySubsumed: List[Proof]) = possiblySubsumed match {
//            case Nil =>
//            case s::tail =>
//          }
//      }
//    }
//
//    val map = new mutable.HashMap[Clause,Proof]
//    def rec3(p: Proof): Unit = {
//      if (!visitedProofs.contains(p)) {
//        if (p.isInstanceOf[Resolvent]) {
//          rec(p.asInstanceOf[Resolvent].left)
//          rec(p.asInstanceOf[Resolvent].right)
//        }
//        map.get(p.clause) match {
//          case None => map += (p.clause -> p)
//          case Some(otherProof) => {
//            if (measure(otherProof) < measure(p)) {
//              otherProof replaces p
//            }
//            else {
//              p replaces otherProof
//              map -= otherProof.clause
//              map += (p.clause -> p)
//            }
//          }
//        }
//        visitedProofs += p
//      }
//    }
//    rec(proof)
//  }
}
