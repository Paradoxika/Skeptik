package skeptik.algorithm.compressor
import skeptik.proof.oldResolution._
import skeptik.proof.oldResolution.defs._
import skeptik.algorithm.compressor.ProofFixing._
import scala.collection._

object UnitLowering {


  private var counter = 0

  private def collectUnits(proof: Proof): mutable.Queue[Proof] = {
    val units = new mutable.Queue[Proof]
    val visitedProofs = new mutable.HashSet[Proof]


    def rec(p: Proof): Unit = {
      if (p.children.forall(c => visitedProofs contains c )) { // ToDo: This can be made more efficient by keeping a callCount

        visitedProofs += p

        counter += 1

        if (p.clause.size == 1 && p.children.length > 1) { // p is a unit with many children
          units += p
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
    rec(proof)
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


