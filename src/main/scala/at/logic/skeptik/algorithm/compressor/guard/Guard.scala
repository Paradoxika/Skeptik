package at.logic.skeptik.algorithm.compressor.guard

import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof._

abstract class Guard [P <: ProofNode[Judgment,P]] extends (Proof[P] => Boolean) {
  self =>
  def &(other: Guard[P]) = new Guard[P] { def apply(r: Proof[P]) = self(r) & other(r) }
}
