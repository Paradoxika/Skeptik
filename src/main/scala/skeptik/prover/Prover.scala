package skeptik.prover

import skeptik.proof.Proof
import skeptik.judgment.Judgment
import scala.collection.immutable.{HashSet => ISet}
import skeptik.proof.ProofNodeCollection


object typeAliases {
  type SideEffectState = Any
  type Calculus[J <: Judgment, P <: Proof[J,P]] = Seq[InferenceRule[J, P]]
  type CalculusWithSideEffects[J <: Judgment, P <: Proof[J,P], S] = Seq[InferenceRuleWithSideEffects[J, P, S]]
}

import typeAliases._

abstract class InferenceRule[J <: Judgment, P <: Proof[J,P]] {
  def apply(premises: Seq[P], conclusion: J): Option[P] // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  def apply(j: J): Seq[Seq[J]] // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.  
}

abstract class InferenceRuleWithSideEffects[J <: Judgment, P <: Proof[J,P], S] {
  def apply(premises: Seq[P], conclusion: J)(implicit c: S): Option[P] // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  def apply(j: J)(implicit c: S): Seq[Seq[(S,J)]] // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
}

class SimpleProver[J <: Judgment, P <: Proof[J,P]](calculus: Calculus[J,P]) {
  // Simple generic bottom-up proof search
  def prove(goal:J) : Option[P] = {
    def proveRec(j: J, seen: ISet[J]): Option[P] = { // "seen" keeps track of goals that already occurred below, in order to detect and prevent cycles.
      val proofs = for (rule <- calculus.par; subGoals <- rule(j).par) yield {
        def proofOf(g: J) = if (seen contains g) None else proveRec(g, seen + j)
        val premises = subGoals.par.map(subGoal => proofOf(subGoal))
        if (premises.seq contains None) None 
        else rule(premises.map(_.get).seq, j)
      }
      proofs.find(_.isInstanceOf[Some[_]]).getOrElse(None)
    }
    proveRec(goal, new ISet[J])
  }
}

class SimpleProverWithSideEffects[J <: Judgment, P <: Proof[J,P]: ClassManifest, S](calculus: CalculusWithSideEffects[J,P,S]) {
  import skeptik.proof._  

  // Simple generic bottom-up proof search
  def prove(goal:J,context:S) : Option[P] = {
    val maxSubgoalSize = 1 * goal.size
    def proveRec(j: J, seen: List[J], c: S): Option[P] = { // "seen" keeps track of goals that already occurred below, in order to detect and prevent cycles.
      //println(j)
      //println(c)
      //println()
      val proofs = for (rule <- calculus; subGoals <- rule(j)(c)) yield {
        println("rule and subgoals")
        println(j)
        println(c)
        println("seen subgoals below")
        seen.map(println _)
        println(rule)
        subGoals.map(println _)
        println()
        def proofOf(g: J, c: S) = 
          if ((seen contains g) || g.size > maxSubgoalSize) {
            println("seenGoal: " + g)
            None
          } 
          else proveRec(g, j::seen, c)
        val premises = subGoals.map({case (state,subGoal) => proofOf(subGoal,state)})
        println()
        System.in.read()
        if (premises.seq contains None) None 
        else {
          val proof = rule(premises.map(_.get).seq, j)(c)
          println(proof)
          println()
          proof
        }
      }
      //val proof = proofs.find(_.isInstanceOf[Some[P]]).getOrElse(None)
      val filteredProofs: Seq[P] = proofs.filter(_ != None).map(_.get)
      
      if (filteredProofs.length == 0) return None
      
      def findShortestProof(seq: Seq[P]): P = {
        var minSize = 999999999
        var minIndex = 0
        for (i <- 0 until seq.length) {
          val p: P = seq(i)
          val size = ProofNodeCollection(p).size
          if (size < minSize) {
            minSize = size
            minIndex = i
          }
        }
        seq(minIndex)
      }
      val proof = findShortestProof(filteredProofs)
      Some(proof)
    }
    proveRec(goal, List[J](), context: S)
  }
}

class SimpleProverWithSideEffects2[J <: Judgment, P <: Proof[J,P]: ClassManifest, S](calculus: CalculusWithSideEffects[J,P,S]) {
  import scala.collection
  def prove(goal:J, context:S) : Option[P] = {
    val maxSubgoalSize = 1 * goal.size
    
    def debug(s: Any)(implicit i:Int) = {
      //println(((1 to i).toList.map(x => "    ") :\ "")(_+_) + s)
    }
    
    
    class B(var b : Boolean) {
      override def toString = b.toString
    }
    
    def proveRec(j: J, seen: List[(J,B)], c: S)(implicit d:Int): Option[P] = {
      debug("")
      if (
          j.size > maxSubgoalSize || 
          seen.exists({case (g,b) => g == j || 
                                     b.b == true
            })) {
        if (seen.exists({case (g,b) => b.b == true})) debug("ABORTED!!!")
        debug(j)
        debug(c)
        debug("seen subgoals below")
        seen.map(debug _)
        debug("seen goal!")
        debug("")
        return None
      } 
      else {
        for (rule <- calculus; subGoals <- rule(j)(c)) yield {
          
          debug(j)
          debug(c)
          debug("seen subgoals below")
          seen.map(debug _)
          debug(rule)
          subGoals.map(debug _)
          //System.in.read()
          debug("")
          val hasBeenProved = new B(false)
          val premises = subGoals.map({case (state,subGoal) => proveRec(subGoal, (j,hasBeenProved)::seen, state)(d+1)})
          debug("")
          if (!premises.contains(None)) {
            hasBeenProved.b = true
            val proof = rule(premises.map(_.get).seq, j)(c)
            debug(proof)
            debug("")
            if (proof.isInstanceOf[Some[_]]) return proof 
          }
        }
        return None
      }
    }
    proveRec(goal, List(), context: S)(0)
  }
}
