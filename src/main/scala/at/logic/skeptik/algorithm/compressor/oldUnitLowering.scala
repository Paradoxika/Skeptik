package at.logic.skeptik.algorithm.compressor
import at.logic.skeptik.proof.oldResolution._
import at.logic.skeptik.proof.oldResolution.defs._
import at.logic.skeptik.algorithm.compressor.ProofNodeFixing._
import collection._
import language.postfixOps

object UnitLowering {


  private var counter = 0

  private def collectUnits(proof: ProofNode): mutable.Queue[ProofNode] = {
    val units = new mutable.Queue[ProofNode]
    val visitedProofNodes = new mutable.HashSet[ProofNode]


    def rec(p: ProofNode): Unit = {
      if (p.children.forall(c => visitedProofNodes contains c )) { // TODO: This can be made more efficient by keeping a callCount

        visitedProofNodes += p

        counter += 1

        if (p.clause.size == 1 && p.children.length > 1) { // p is a unit with many children
          units += p
          for (c <- p.children) {
            if (p == c.left) deletedSubProofNode replacesLeftParentOf c
            else deletedSubProofNode replacesRightParentOf c
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
    rec(proof)
    counter = 0
    units
  }

  private def reinsertUnits(proof: ProofNode, units: mutable.Queue[ProofNode]): ProofNode = {
    if (units.length == 0) proof
    else {
      val u = units.dequeue
      //println("reinserting: " + u.id + ": " +  u.clause + " ; " + proof.id + ": " +  proof.clause)
      val newRootProofNode = try {
        val p = new Resolvent(proof, u)
        p.pivot
        p
      } catch {
        case _: Throwable => {println(u.clause + " failed to resolve"); proof}
      }
      reinsertUnits(newRootProofNode, units)
    }
    //println("new root clause: " + newRootProofNode.clause)
  }
    

  def lowerUnits(p: ProofNode): ProofNode = {
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
    val fixedUnits = new mutable.Queue[ProofNode]
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


