package at.logic.skeptik.prover

import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.util.debug._
import at.logic.skeptik.util.math.argMin
import reflect.ClassTag

// ToDo: (B) Use futures and Map from (goal, inference) to future to create DAG-proof!
class SimpleProver[J <: Judgment, P <: ProofNode[J,P]: ClassTag](calculus: Calculus[J,P]) {
  def prove(goal:J, timeout: Long = Long.MaxValue, maxheight: Int = Int.MaxValue) : Option[P] = {
    val deadline = System.nanoTime + timeout * 1000000

    def proveRec(j: J, seen: Set[J])(implicit d:Int): Option[P] = {
      //debug(j)
      
      if (System.nanoTime > deadline) {
        //debug("timeout")
        return None
      } 
      else if (seen contains j) {
        //debug("cycle")
        return None
      } 
      else if (j.logicalSize > goal.logicalSize) {
        //debug("goal size excess")
        return None
      } 
      else if (d > maxheight) { // avoids cycles and limits height
        //debug("max height"); 
        return None
      }
      else {
        //debug("ok")
        //debug("subgoal: " + j)
        
        
        var bestProof: Option[P] = None
        
        val bestProofs = for (rule <- calculus) yield {
          //debug("trying rule: " + rule)
          
          val subGoalsSeq = rule(j)
          //debug("generated alternative subgoals: ")
          //subGoalsSeq map {debug _}
          //debug("")
          val premisesSeq = for (subGoals <- subGoalsSeq) yield {
            subGoals map {subGoal => proveRec(subGoal, seen + j)(d+1)}
          }
          //debug("premisesSeq: " + premisesSeq)
          //debug("")
          val filteredPremisesSeq = premisesSeq filter { premises => ! (premises contains None) }
          //debug("filteredPremisesSeq: " + filteredPremisesSeq)
          //debug("")
          
          val proofSeq = filteredPremisesSeq map { premises => rule(premises.map(_.get).seq, j)}
          //debug("proofSeq: " + proofSeq)
          //debug("")
          var bestProofForRule: Option[P] = None
          var bestProofForRuleSize = Int.MaxValue
          for (pOption <- proofSeq) {
            //debug(pOption)
            
            pOption match { 
              case Some(p) => {
                val pSize = Proof(p).size
                if (pSize < bestProofForRuleSize) {
                  bestProofForRuleSize = pSize
                  bestProofForRule = pOption
                }
              }
              case None => 
            }
          }
          
          //debug("bestProofForRule: " + bestProofForRule)
          //debug("")
          bestProofForRule
        }
 
        var bestProofSize = Int.MaxValue
        for (pOption <- bestProofs) {
          pOption match {
              case Some(p) => {
                val pSize = Proof(p).size
                if (pSize < bestProofSize) {
                  bestProofSize = pSize
                  bestProof = pOption
                }
              }
              case None => 
          }
        }
        //debug("bestProof: " + bestProof)
        //debug("")
        
        bestProof
      }
//      else {
//        val proofs = for (rule <- calculus; subGoals <- rule(j)) yield {
//          debug(j); 
//          debug("subgoals below"); seen.toList.reverse.map(debug _); 
//          debug(rule); subGoals.map(debug _); 
//          debug("")
//          val premises = subGoals map {subGoal => proveRec(subGoal, seen + j)(d+1)} 
//          debug("")
//          if (!premises.contains(None)) {
//            val proof = rule(premises.map(_.get).seq, j)
//            debug(proof); 
//            debug("")
//            proof
//          }
//          else None
//        }
//
//        debug(j)
//        debug(proofs)
//        
//        argMin(proofs.filter(_ != None).map(_.asInstanceOf[Some[P]].get).toList,
//               (p: P) => Proof(p).size)
//      }
    }
    proveRec(goal, Set())(0)
  }
}