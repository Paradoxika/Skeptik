package at.logic.skeptik.prover

import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.Proof
//import at.logic.skeptik.util.debug._
//import at.logic.skeptik.util.math.argMin
import reflect.ClassTag

import collection.mutable.{Queue, HashMap => MMap}




class SimpleSaturationProver[J <: Judgment, P <: ProofNode[J,P]: ClassTag]
      (unaryRules: SaturationCalculus[J,P], binaryRules: SaturationCalculus[J,P]) {
  def saturate(axioms:Seq[P], goal: J) : Option[P] = {
    val unprocessed = new Queue[P]() ++ axioms
    val processed = new Queue[P]()
    
    val proofLengths = new MMap[J, Int]()
    for (a <- axioms) {proofLengths(a.conclusion) = Proof(a).size }
    
    var result: Option[P] = unprocessed find {p => p.conclusion == goal} // checks whether the axioms already contain the goal.  
    var notFound = (result == None)
    
    var iterations = 0
    
    while (notFound && ! unprocessed.isEmpty && iterations < 3000) {
      iterations = iterations + 1
      
      val newlyDerived = new Queue[P]()
      
      val selected = unprocessed.dequeue()
      
      println()
      println("selected:   " + selected.conclusion  + "   length: " +  Proof(selected).size )
      
      for (r <- unaryRules) newlyDerived ++= r(Seq(selected))
      
      for (p <- processed; r <- binaryRules) {
        newlyDerived ++= r(Seq(selected,p))
        newlyDerived ++= r(Seq(p,selected))
      }
  
      
      // filter redundant newly derived
      val filteredNewlyDerived = newlyDerived filter { p => 
        val length = Proof(p).size 
     
        proofLengths.get(p.conclusion) match {
          case None => { proofLengths(p.conclusion) = length; true }
          case Some(l) => if (l > length) { proofLengths(p.conclusion) = length; true } else false
        }
      }
      
      
      
      
      
      println("filtered newly derived:")
      for (n <- filteredNewlyDerived) println(n.conclusion  + "   length: " +  Proof(n).size )
      
      processed += selected
      unprocessed ++= filteredNewlyDerived
      
      result = filteredNewlyDerived find {p => p.conclusion == goal}
      notFound = (result == None)
    }
    return result
  }
}