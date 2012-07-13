package at.logic.skeptik.prover

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.judgment.Judgment

abstract class Prover[J <: Judgment, P <: Proof[J,P]] {
  def calculus: Calculus[J,P]
  
  def prove(goal: J): Option[P]
}