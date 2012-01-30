/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import proofCompression.ResolutionCalculus.measures._
import proofCompression.Utilities._
import proofCompression.ProofFixing._
import scala.collection._

object UnitLowering {

  private var counter = 0

  private def collectUnits(proof: Proof): mutable.Queue[Proof] = {
    val units = new mutable.Queue[Proof]
    val visitedProofs = new mutable.HashSet[Proof]


//    val callCount = new mutable.HashMap[Proof,Int]
//    callCount += (proof -> -1)
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
//    def resetCallCount(p:Proof) = callCount -= p


    def rec(p: Proof): Unit = {
      //increaseCallCount(p)
      if (p.children.forall(c => visitedProofs contains c )) { // ToDo: This can be made more efficient by keeping a callCount
        //resetCallCount(p)
        visitedProofs += p

        counter += 1

        if (p.clause.size == 1 && p.children.length > 1) { // p is a unit with many children
          units += p
          //println(units.length)
          for (c <- p.children) {
            if (p == c.left) deletedSubProof replacesLeftParentOf c
            else deletedSubProof replacesRightParentOf c
          }
          //require( p.children == Nil )
        }
        p match {
          case i: Input => 
          case r: Resolvent => {
            rec(r.left)
            rec(r.right)
          }
        }
      }
    }
    val k = length(proof)
    println("proof length: " + length(proof))
    rec(proof)
    println(counter)
    if (counter < k) println("ops!")
    println("proof length: " + length(proof))
    //println(units.length)
    //println((units.map(p => p.length) :\ proof.length)((x,y) => x+y) )
    counter = 0
    units
  }

  private def reinsertUnits(proof: Proof, units: mutable.Queue[Proof]): Proof = {
    if (units.length == 0) proof
    else {
      val u = units.dequeue
      //println("reinserting: " + u.id + ": " +  u.clause + " ; " + proof.id + ": " +  proof.clause)
      val newRootProof = try {
        val p = new Resolvent(proof, u)
        p.pivot
        p
      } catch {
        case _ => {println(u.clause + " failed to resolve"); proof}
      }
      reinsertUnits(newRootProof, units)
    }
    //println("new root clause: " + newRootProof.clause)
  }

  //private def reinsertUnitsFunctional(proof: Proof, units: mutable.Queue[Proof]): Proof = (proof /: units) ((p, u) => try {new Resolvent(p, u)} catch {case _ => {println(u.clause + " failed to resolve"); p}})
    

  def lowerUnits(p: Proof): Proof = {
    //println("collecting units")
    val units = collectUnits(p)
    //println("units: " + units.map(u => u.id + ": " + u.clause))
    //println(units.length)
    //println("end clause (after unit collection): " + p.id + " ; " + p.clause)
    val roots = p::units.toList
    //println("fixing proofs")
    val fixedRoots = fixTopDown(roots)
    //for (r <- fixedRoots) println(r.id)
    val fixedP = fixedRoots.head
    val fixedUnits = new mutable.Queue[Proof]
    fixedUnits ++= fixedRoots.tail
    //println(fixedUnits.length)
    //println("units (after fixing): " + fixedUnits.map(u => u.id + ": " + u.clause))
    //println("end clause (after fixing): " + fixedP.id + " ; " + fixedP.clause)
    //println("reinserting units")
    val result = reinsertUnits(fixedP, fixedUnits)
    //println("end clause (after reinsertion): " + result.id + " ; " + result.clause)
    require(result.clause isEmpty)
    result
  }
}


