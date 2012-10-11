package at.logic.skeptik

import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.judgment.Judgment

package object prover {
  type Calculus[J <: Judgment, P <: ProofNode[J,P]] = Seq[InferenceRule[J, P]]
}