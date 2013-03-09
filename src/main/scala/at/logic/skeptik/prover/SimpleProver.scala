package at.logic.skeptik.prover

import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.util.debug._
import at.logic.skeptik.util.math.argMin
import reflect.ClassTag

// ToDo: (B) Use futures and Map from (goal, inference) to future to create DAG-proof!
class SimpleProver[J <: Judgment, P <: ProofNode[J,P]: ClassTag](calculus: Calculus[J,P]) {
  def prove(goal:J, timeout: Long = Long.MaxValue) : Option[P] = {
    val deadline = System.nanoTime + timeout * 1000000 
    
    def proveRec(j: J, seen: Set[J])(implicit d:Int): Option[P] = {
      if (System.nanoTime > deadline || (seen contains j) || j.logicalSize > goal.logicalSize) { // avoids cycles
        debug(j); debug("seen subgoals below"); seen.map(debug _); debug("seen goal!"); debug("")
        return None
      } 
      else {
        val proofs = for (rule <- calculus; subGoals <- rule(j)) yield {         
          debug(j); debug("subgoals below"); seen.toList.reverse.map(debug _); debug(rule); subGoals.map(debug _); debug("")
          val premises = subGoals.map({subGoal => proveRec(subGoal, seen + j)(d+1)})
          debug("")
          if (!premises.contains(None)) {
            val proof = rule(premises.map(_.get).seq, j)
            debug(proof); debug("")
            proof
          }
          else None
        }

        argMin(proofs.filter(_ != None).map(_.asInstanceOf[Some[P]].get).toList, 
               (p: P) => Proof(p).size)
      }
    }
    proveRec(goal, Set())(0)
  }
}