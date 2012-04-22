package ResK.algorithms


object NewUnitLowering {
  import ResK.proofs._
  import ResK.judgments.Sequent
  import ResK.calculi.resolution.measures._
  import ResK.algorithms.ProofFixing._
  import scala.collection.mutable.{Queue, HashMap => MMap}
  //import scala.collection.immutable.{HashSet => ISet}

  private def collectUnits(proof: SequentProof): Queue[SequentProof] = {
    val units = new Queue[SequentProof]  
    val childrenOf = new MMap[SequentProof,List[SequentProof]]
    def addChild(p: SequentProof, child:SequentProof) = childrenOf.update(p, child::childrenOf.getOrElse(p,Nil))
    def isUnitClause(s:Sequent) = s.ant.length + s.suc.length == 1
    def visit(ps: Proof[Sequent], l:List[Any]) = {
      // ToDo: casting is necessary, due to the contravariance in the function argument of bottomUp. The traversals are still not convenient and elegant enough.
      val p = ps.asInstanceOf[SequentProof]
      for (premise <- p.premises) 
        addChild(premise,p)
      if (isUnitClause(p.conclusion) && childrenOf(p).length > 1) units += p
    }
    traversal.bottomUp(proof,visit)
    units
  }

  private def moveUnitsDown(proof: SequentProof, units: Queue[SequentProof]): SequentProof = {
    val unitsSet = units.toSet
    val fixMap = new MMap[SequentProof,SequentProof]
    
    def visit(ps:Proof[Sequent],fixedPremises:List[SequentProof]) = {
      val p = ps.asInstanceOf[SequentProof]
      val fixedLeft = fixedPremises.head; val fixedRight = fixedPremises.last;
      val fixedP = p match {
        case Axiom(conclusion) => Axiom(conclusion)
        case CutIC(left,right,_,_) if unitsSet contains left => fixedRight
        case CutIC(left,right,_,_) if unitsSet contains right => fixedLeft
        case CutIC(left,right,auxL,auxR) => ((fixedLeft.conclusion.suc contains auxL),(fixedRight.conclusion.suc contains auxR)) match {
          case (true,true) => CutIC(fixedPremises.head,fixedPremises.last,auxL,auxR)
          case (true,false) => fixedRight
          case (false,true) => fixedLeft
          case (false,false) => fixedLeft // ToDo: choosing left arbitrarily here. Should choose the smallest proof though.
        }
        case _ => throw new Exception("Unsupported inference rule encountered while lowering units")
      }
      if ((unitsSet contains p) || (p == proof)) fixMap += (p -> fixedP)
      fixedP
    }
    traversal.topDown(proof,visit)
    units.map(fixMap).foldLeft(fixMap(proof))( (left,right) => try {CutIC(left,right)} catch { case e: Exception => left })
  }
    

  def apply(proof: SequentProof): SequentProof = moveUnitsDown(proof,collectUnits(proof))
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


