package at.logic.skeptik.algorithm.compressor.guard

import at.logic.skeptik.proof._

abstract class Guard [P <: Proof[_,P]] extends (ProofNodeCollection[P] => Boolean) {
  self =>
  def &(other: Guard[P]) = new Guard[P] { def apply(r: ProofNodeCollection[P]) = self(r) & other(r) }
}
