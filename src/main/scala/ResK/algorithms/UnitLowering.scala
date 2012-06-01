package ResK.algorithms

object NewUnitLowering extends Function1[ResK.proofs.SequentProof,ResK.proofs.SequentProof] {
  import ResK.proofs._
  import ResK.judgments.Sequent
  import ResK.calculi.resolution.measures._
  import ResK.algorithms.ProofFixing._
  import scala.collection.mutable.{Queue, HashMap => MMap}

  // made public for debug. TODO: private
  def collectUnits(proofs: ProofNodeCollection[SequentProof]) = {
    def isUnitClause(s:Sequent) = s.ant.length + s.suc.length == 1
    proofs.foldRight(Nil:List[SequentProof])((p, acc) =>
      if (isUnitClause(p.conclusion) && proofs.childrenOf(p).length > 1) p::acc else acc
    );
  }

  // made public for debug. TODO: private
  def fixProofs(unitsSet: Set[SequentProof], proofs: ProofNodeCollection[SequentProof]) = {
    val fixMap = MMap[SequentProof,SequentProof]()

    def visit (p: SequentProof, fixedPremises: List[SequentProof]) = {
      lazy val fixedLeft  = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;
      val fixedP = p match {
        case Axiom(conclusion) => Axiom(conclusion)
        case CutIC(left,right,_,_) if unitsSet contains left => fixedRight
        case CutIC(left,right,_,_) if unitsSet contains right => fixedLeft
        case CutIC(left,right,auxL,auxR) => CutIC(fixedLeft, fixedRight, auxL, auxR)
//      case CutIC(left,right,auxL,auxR) => ((fixedLeft.conclusion.suc  contains auxL),
//                                           (fixedRight.conclusion.ant contains auxR)) match {
//        case (true,true) => CutIC(fixedLeft, fixedRight, auxL, auxR)
//        case (true,false) => println(p.conclusion + " -> " + fixedRight.conclusion) ; fixedRight
//        case (false,true) => println(p.conclusion + " -> " + fixedLeft.conclusion) ; fixedLeft
//        case (false,false) => println("cata") ; fixedLeft // ToDo: choosing left arbitrarily here. Should choose the smallest proof though.
      }
      if (p == proofs.root || unitsSet.contains(p)) fixMap.update(p, fixedP)
      fixedP
    }
    proofs.foldDown(visit)
    fixMap
  }

  def apply(p: SequentProof) = {
    val proofs  = ProofNodeCollection(p)
    val units   = collectUnits(proofs)
    val fixMap  = fixProofs(units.toSet, proofs)
    units.map(fixMap).foldLeft(fixMap(p))((left,right) => try {CutIC(left,right)} catch {case e:Exception => left})
  }
}



object UnitLowering {
  import ResK.calculi.resolution._
  import ResK.calculi.resolution.measures._
  import ResK.algorithms.ProofFixing._
  import scala.collection._

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


