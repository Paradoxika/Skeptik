package skeptik.prover

import skeptik.proof.Proof
import skeptik.judgment.Judgment
import scala.collection.immutable.{HashSet => ISet}
import skeptik.proof.ProofNodeCollection
import skeptik.util.debug._


object typeAliases {
  type Calculus[J <: Judgment, P <: Proof[J,P]] = Seq[InferenceRule[J, P]]
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

class SimpleProver2[J <: Judgment, P <: Proof[J,P]: ClassManifest, S](calculus: Calculus[J,P]) {
  def prove(goal:J) : Option[P] = {
    val maxSubgoalSize = 3 * goal.size
    
    def proveRec(j: J, seen: Set[J])(implicit d:Int): Option[P] = {
      if (seen contains j) { // avoids cycles
        debug(j); debug("seen subgoals below"); seen.map(debug _); debug("seen goal!"); debug("")
        return None
      } 
      else {
        // TODO: (Bruno) the prover doesn't terminate if "calculus.par" is used.
        for (rule <- calculus; subGoals <- rule(j).par) yield {         
          debug(j); debug("seen subgoals below"); seen.map(debug _); debug(rule); subGoals.map(debug _); debug("")
          val premises = subGoals.map({subGoal => proveRec(subGoal, seen + j)(d+1)})
          debug("")
          if (!premises.contains(None)) {
            val proof = rule(premises.map(_.get).seq, j)
            debug(proof); debug("")
            if (proof.isInstanceOf[Some[_]]) return proof 
          }
        }
        return None
      }
    }
    proveRec(goal, Set())(0)
  }
}