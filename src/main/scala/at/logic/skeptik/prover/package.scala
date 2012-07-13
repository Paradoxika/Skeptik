package at.logic.skeptik

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.judgment.Judgment

package object prover {
  type Calculus[J <: Judgment, P <: Proof[J,P]] = Seq[InferenceRule[J, P]]
}