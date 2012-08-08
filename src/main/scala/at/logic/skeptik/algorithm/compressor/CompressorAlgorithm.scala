package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.compressor.guard._


/* Base trait. Every concrete algorithm must extends it.
 */
trait CompressorAlgorithm [P <: Proof[_,P]]
{

  def apply(proof: ProofNodeCollection[P]):ProofNodeCollection[P]

  def apply(proof: ProofNodeCollection[P], guard: Guard[P]):ProofNodeCollection[P]

}

/* Every algorithm that should never be called iteratively should inherit that
 * trait.
 */
trait IdempotentAlgorithm [P <: Proof[_,P]]
extends CompressorAlgorithm[P] {

  def apply(proof: ProofNodeCollection[P], guard: Guard[P]):ProofNodeCollection[P] = {
    val compressedProof = apply(proof)
    guard(compressedProof)
    compressedProof
  }

}

/* Every algorithm that could be called iteratively should inherit that trait.
 */
trait RepeatableAlgorithm [P <: Proof[_,P]]
extends CompressorAlgorithm[P] {

  def apply(proof: ProofNodeCollection[P], guard: Guard[P]):ProofNodeCollection[P] = {
    var currentProof = proof
    do {
      currentProof = apply(proof)
    } while (guard(currentProof))
    currentProof
  }

}

/* Algorithms which does compress the proof during a finite number of iterations
 * but become idempotent thereafter.
 */
trait RepeatableWhileCompressingAlgorithm [P <: Proof[_,P]]
extends RepeatableAlgorithm[P] {

  private def internalGuard(initialProof: ProofNodeCollection[P]) = new Guard[P] {
    var lastSize = initialProof.size
    def apply(r: ProofNodeCollection[P]) = (lastSize > r.size) && { lastSize = r.size ; true }
  }

  override def apply(proof: ProofNodeCollection[P], guard: Guard[P]):ProofNodeCollection[P] = 
    super.apply(proof, internalGuard(proof) & guard)

}

/* Non-deterministic algorithms which might produce proof bigger than the
 * original.
 */
trait RandomCompressionRepeatableAlgorithm [P <: Proof[_,P]]
extends RepeatableAlgorithm[P] {

  override def apply(initialProof: ProofNodeCollection[P], guard: Guard[P]):ProofNodeCollection[P] = {
    var currentProof = initialProof
    do {
      val compressedProof = apply(initialProof)
      if (compressedProof.size < currentProof.size) currentProof = compressedProof
    } while (guard(currentProof))
    currentProof
  }

}
