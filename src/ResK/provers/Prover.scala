package ResK.provers

import ResK.proofs.Proof
import ResK.judgments.Judgment
//import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashSet => ISet}


object typeAliases {
  type SideEffectState = Any
  type Calculus[J <: Judgment, P <: Proof[J,P]] = Seq[InferenceRule[J, P]]
  type CalculusWithSideEffects[J <: Judgment, P <: Proof[J,P], S] = Seq[InferenceRuleWithSideEffects[J, P, S]]
}

import typeAliases._

abstract class InferenceRule[J <: Judgment, P <: Proof[J,P]] {
  def apply(premises: Seq[P], conclusion: J): Option[P] // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  def apply(j: J): Seq[Seq[J]] // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.  
//def apply(premises: Seq[P]) : Seq[P] 
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
      proofs.find(_.isInstanceOf[Some[P]]).getOrElse(None)
    }
    proveRec(goal, new ISet[J])
  }
    // Simple generic top-down proof search
  def prove(axioms: Seq[P], target: J): Option[P] = {
    None // ToDo
  }
}

class SimpleProverWithSideEffects[J <: Judgment, P <: Proof[J,P], S](calculus: CalculusWithSideEffects[J,P,S]) {
  // Simple generic bottom-up proof search
  def prove(goal:J,context:S) : Option[P] = {
    def proveRec(j: J, seen: ISet[J], c: S): Option[P] = { // "seen" keeps track of goals that already occurred below, in order to detect and prevent cycles.
      val proofs = for (rule <- calculus.par; subGoals <- rule(j)(c).par) yield {
        def proofOf(g: J, c: S) = if (seen contains g) None else proveRec(g, seen + j, c)
        val premises = subGoals.par.map({case (state,subGoal) => proofOf(subGoal,state)})
        if (premises.seq contains None) None 
        else rule(premises.map(_.get).seq, j)(c)
      }
      proofs.find(_.isInstanceOf[Some[P]]).getOrElse(None)
    }
    proveRec(goal, new ISet[J], context: S)
  }
}