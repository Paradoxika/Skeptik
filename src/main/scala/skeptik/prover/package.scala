package skeptik

import skeptik.proof.Proof
import skeptik.judgment.Judgment

package object prover {
  type Calculus[J <: Judgment, P <: Proof[J,P]] = Seq[InferenceRule[J, P]]
}