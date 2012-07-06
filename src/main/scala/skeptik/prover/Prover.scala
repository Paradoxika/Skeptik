package skeptik.prover

import skeptik.proof.Proof
import skeptik.judgment.Judgment

abstract class Prover[J <: Judgment, P <: Proof[J,P]] {
  def calculus: Calculus[J,P]
  
  def prove(goal: J): Option[P]
}