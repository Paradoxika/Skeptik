package at.logic.skeptik.algorithm.compressor.guard

import at.logic.skeptik.proof._

abstract class Guard [P <: Proof[_,P]] extends (ProofNodeCollection[P] => Boolean) {
  def &(other: Guard[P]) = new Guard[P] { def apply(r: ProofNodeCollection[P]) = this(r) & other(r) }
}
