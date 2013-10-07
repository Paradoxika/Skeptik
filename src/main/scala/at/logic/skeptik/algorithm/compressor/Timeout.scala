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
    var count = 0
    while ((System.nanoTime() - start)/1000000 < timeout) { count += 1 ; result = applyOnce(result) }
    print("("+count+" times)")
    return result
  }
}

/**
 * The algorithm should applied only once and not until a timeout is reached.
 */
trait outTimeout {
  def applyOnce(p: Proof[N]): Proof[N]
  def apply(p: Proof[N]): Proof[N] = {
    applyOnce(p)
  }
}