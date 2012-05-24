package ResK.provers

import ResK.proofs.Proof
import ResK.judgments.Judgment
//import scala.collection.mutable.{HashSet => MSet}

object typeAliases {
  type Calculus[J <: Judgment, P <: Proof[J,P]] = Seq[InferenceRule[J, P]]
}

import typeAliases._

abstract class InferenceRule[J <: Judgment, P <: Proof[J,P]] {
  def apply(j: J): Seq[Seq[J]] // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(premises: Seq[P], conclusion: J): Option[P] // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  //def apply(premises: Seq[P]) : Seq[P] 
}

class SimpleProver[J <: Judgment, P <: Proof[J,P]](calculus: Calculus[J,P]) {
  // Simple generic bottom-up proof search
  def prove(j: J): Option[P] = {
    val proofs: Seq[Option[P]] = for (rule <- calculus; subGoals <- rule(j)) yield {
      val premises = for (subGoal <- subGoals) yield (new SimpleProver(calculus)).prove(subGoal)
      if (premises contains None) None 
      else rule(premises.map(_.get), j)
    }
    proofs.find(_.isInstanceOf[Some[P]]).getOrElse(None)
  }
  
  // Simple generic top-down proof search
  def prove(axioms: Seq[P], target: J): Option[P] = {
    None // ToDo
  }
}
