/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import proofCompression.Utilities._
import proofCompression.ProofFixing._
import scala.collection._

object UnitLowering {
  private def collectUnits(proof: Proof): mutable.Queue[Proof] = {
    val units = new mutable.Queue[Proof]
    val visitedProofs = new mutable.HashSet[Proof]

    def hasReceivedAllCalls(p: Proof) = p.children.forall(c => visitedProofs contains c ) // ToDo: This can be made more efficient by keeping a callCount

    def rec(p: Proof): Unit = {
      if (hasReceivedAllCalls(p)) {
        visitedProofs += p
        if (p.clause.size == 1 && p.children.length > 1) { // p is a unit with many children
          units += p
          for (c <- p.children) {
            if (p == c.left) c.left = deletedSubProof
            else c.right = deletedSubProof
          }
          p.children = Nil
        }
        p match {
          case i: Input => return
          case r: Resolvent => {
            rec(r.left)
            rec(r.right)
          }
        }
      }
    }
    rec(proof)
    units
  }

  private def reinsertUnits(proof: Proof, units: mutable.Queue[Proof]): Proof = {
    val u = units.dequeue
    val newRootProof = new Resolvent(proof, u)
    if (units.length == 0) newRootProof
    else reinsertUnits(newRootProof, units)
  }

  private def reinsertUnitsFunctional(proof: Proof, units: mutable.Queue[Proof]): Proof = (proof /: units) ((p, u) => new Resolvent(p,u))
    

  def lowerUnits(p: Proof) = {
    val units = collectUnits(p)
    fix(p)
    reinsertUnits(p, units)
  }
}


//  def regularizationRecSchema(p: Proof, callingChild: Resolvent, litB: Option[List[Literal]], continuation: Resolvent => Unit): Unit = {
//    p match {
//      case Input(_) => return
//      case Resolvent(left,right) => {
//        val r = p.asInstanceOf[Resolvent]
//        litB match {
//          case None => p.children = p.children - callingChild   // Calling Child is orphan of the called Parent
//          case Some(literalsB) => p.literalsBelow += (callingChild -> literalsB)
//        }
//        def hasReceivedAllCalls = p.children.forall(c => p.literalsBelow.contains(c))
//        if (hasReceivedAllCalls) continuation(r)
//      }
//    }
//  }

//
//    val callCount = new mutable.HashMap[Proof,Int]
//    callCount += (proof -> 0)
//
//    def increaseCallCount(p:Proof) = {
//      callCount.get(p) match {
//        case None => callCount += (p -> 1)
//        case Some(i) => {
//          callCount -= p
//          callCount += (p -> (i+1))
//        }
//      }
//    }
//    def decreaseCallCount(p:Proof) = {
//      callCount.get(p) match {
//        case None => callCount += (p -> 1)
//        case Some(i) => {
//          callCount -= p
//          callCount += (p -> (i-1))
//        }
//      }
//    }