package at.logic.skeptik.prover

import at.logic.skeptik.proof.ProofNode
import at.logic.skeptik.judgment.Judgment

abstract class Prover[J <: Judgment, P <: ProofNode[J,P]] {
  def calculus: Calculus[J,P]
  
  def prove(goal: J): Option[P]
}