package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.compressor.guard._

// ToDo: should check the possibility/desirability of making ProofCompressor inherit from Function1
/* Base class. Every concrete algorithm must extend it.
 */
abstract class ProofCompressor [P <: ProofNode[_,P]]
{

  def apply(proof: Proof[P]):Proof[P]

  def apply(proof: Proof[P], guard: Guard[P]):Proof[P]

  def *(a: ProofCompressor[P]) = {} // ToDo: should return a sequential composition
  
  def ~(a: ProofCompressor[P]) = {} // ToDo: should run both and return the best proof produced
}

/* Every algorithm that should never be called iteratively should inherit this
 * trait.
 */
trait IdempotentAlgorithm [P <: ProofNode[_,P]]
extends ProofCompressor[P] {

  def apply(proof: Proof[P], guard: Guard[P]):Proof[P] = {
    val compressedProof = apply(proof)
    guard(compressedProof)
    compressedProof
  }

}

object IdempotentAlgorithm {
  def apply[P <: ProofNode[_,P]](algos: ProofCompressor[P]*) = new IdempotentAlgorithm[P] {
    def apply(proof: Proof[P]) = algos.foldRight(proof) { (fct, result) => fct(result,once) }
  }
}

/* Every algorithm that could be called iteratively should inherit that trait.
 */
trait RepeatableAlgorithm [P <: ProofNode[_,P]]
extends ProofCompressor[P] {

  def apply(proof: Proof[P], guard: Guard[P]):Proof[P] = {
    var currentProofNode = proof
    do {
      currentProofNode = apply(currentProofNode)
    } while (guard(currentProofNode))
    currentProofNode
  }

}

/* Algorithms that compress the proof during a finite number of iterations
 * but become idempotent thereafter.
 */
trait RepeatableWhileCompressingAlgorithm [P <: ProofNode[_,P]]
extends RepeatableAlgorithm[P] {

  private def internalGuard(initialProofNode: Proof[P]) = new Guard[P] {
    var lastSize = initialProofNode.size
    def apply(r: Proof[P]) = (lastSize > r.size) && { lastSize = r.size ; true }
  }

  override def apply(proof: Proof[P], guard: Guard[P]):Proof[P] = 
    super.apply(proof, internalGuard(proof) & guard)

}

object RepeatableWhileCompressingAlgorithm {
  def apply[P <: ProofNode[_,P]](algos: ProofCompressor[P]*) = new RepeatableWhileCompressingAlgorithm[P] {
    def apply(proof: Proof[P]) = algos.foldRight(proof) { (fct, result) => fct(result,once) }
  }
}


/* Non-deterministic algorithms which might produce proof bigger than the
 * original.
 */
trait RandomCompressionRepeatableAlgorithm [P <: ProofNode[_,P]]
extends RepeatableAlgorithm[P] {

  override def apply(initialProofNode: Proof[P], guard: Guard[P]):Proof[P] = {
    var currentProofNode = initialProofNode
    do {
      val compressedProofNode = apply(currentProofNode)
      if (compressedProofNode.size < currentProofNode.size) currentProofNode = compressedProofNode
    } while (guard(currentProofNode))
    currentProofNode
  }

}
