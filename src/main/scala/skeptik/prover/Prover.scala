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
    def proveRec(j: J, seen: ISet[J], c: S): Option[P] = { // "seen" keeps track of goals that already occurred below, in order to detect and prevent cycles.
      val proofs = for (rule <- calculus; subGoals <- rule(j)(c)) yield {
        def proofOf(g: J, c: S) = if (seen contains g) None else proveRec(g, seen + j, c)
        val premises = subGoals.map({case (state,subGoal) => proofOf(subGoal,state)})
        if (premises.seq contains None) None 
        else {
          val proof = rule(premises.map(_.get).seq, j)(c)
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
    proveRec(goal, new ISet[J], context: S)
  }
}
