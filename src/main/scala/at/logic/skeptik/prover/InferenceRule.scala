package at.logic.skeptik.prover

import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.judgment.Judgment


trait InferenceRule[J <: Judgment, P <: ProofNode[J,P]] {
  def apply(premises: Seq[P], conclusion: J): Option[P] // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
  def apply(j: J): Seq[Seq[J]] // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.  
}

trait SaturationInferenceRule[J <: Judgment, P <: ProofNode[J,P]] {
  def apply(premises: Seq[P]): Seq[P] // applies the rule on the premises in all possible ways.
}