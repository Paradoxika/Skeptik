package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}

trait Timeout {
  def timeout: Int // in milliseconds
  def applyOnce(p: Proof[N]): Proof[N]
  def apply(p: Proof[N]): Proof[N] = {
    val start = System.nanoTime()
    var result = p
    while ((System.nanoTime() - start)/1000000 < timeout) result = applyOnce(result)
    return result
  }
}