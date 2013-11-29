package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.algorithm.compressor.Timeout

/** Terminates the Reduce-and-Reconstruct algorithm after a given amount of time.
 */
trait TimeoutTermination
extends Reconstruct with Timeout {
  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, reduce))
}
