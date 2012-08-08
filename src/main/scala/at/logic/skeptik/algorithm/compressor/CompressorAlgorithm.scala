package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof._

/* I've put everything in the same file for now. I think it'll be easier for
 * you to review. Comments explain where I plan to dispatch some parts later.
 */





/* All this conversions should of course be moved to package object files
 */
object conversions {

  /* Scala forbids to inherit from different fucntion traits. As a workaround,
   * some implicit conversion are provided.
   *
   * to algorithm/compressor/package.scala.
   */

  /* AbstratcCompressorAlgorithm to (ProofNodeCollection[P] => ProofNodeCollection[P]) */
  implicit def compressorAlgorithmToFunctionProofNodeCollection[P <: Proof[_,P]](a: AbstractCompressorAlgorithm[P]) =
    { (p: ProofNodeCollection[P]) => a(p) }

  /* AbstratcCompressorAlgorithm to ((ProofNodeCollection[P], Guard[P]) => ProofNodeCollection[P]) */
  implicit def compressorAlgorithmToFunctionProofNodeCollectionWithGuard[P <: Proof[_,P]](a: AbstractCompressorAlgorithm[P]) =
    { (p: ProofNodeCollection[P], g: Guard[P]) => a(p,g) }
  
  /* to algorithm/compressor/guard/package.scala.
   */

  /* (ProofNodeCollection => Boolean) to Guard[Proof] */
  implicit def proofFctToGuard[P <: Proof[_,P]](fct: ProofNodeCollection[P] => Boolean) = new Guard[P] { def apply(r: ProofNodeCollection[P]) = fct(r) }

  /* (() => Boolean) to Guard[_] */
  implicit def fctToGuard[P <: Proof[_,P]](fct: () => Boolean) = new Guard[P] { def apply(r: ProofNodeCollection[P]) = fct() }

}

import conversions._





/* Base trait for CompressorAlgorithm. Concrete algorithms should inherit it
 * directly only if they want to profit from ProofNodeCollection. If only node
 * collection is needed, please use CompressorAlgorithm instead.
 */
trait AbstractCompressorAlgorithm [P <: Proof[_,P]]
{

  def apply(proof: ProofNodeCollection[P]):ProofNodeCollection[P]

  def apply(proof: ProofNodeCollection[P], guard: Guard[P]):ProofNodeCollection[P]

}

/* Every algorithm that should never be called iteratively should inherit that
 * trait.
 */
trait IdempotentAlgorithm [P <: Proof[_,P]]
extends AbstractCompressorAlgorithm[P] {

  def apply(proof: ProofNodeCollection[P], guard: Guard[P]):ProofNodeCollection[P] = {
    val compressedProof = apply(proof)
    guard(compressedProof)
    compressedProof
  }

}

/* Every algorithm that could be called iteratively should inherit that trait.
 */
trait RepeatableAlgorithm [P <: Proof[_,P]]
extends AbstractCompressorAlgorithm[P] {

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





/* I plan to move Guard to algorithm/compressor/guard/Guard.scala.
 */
abstract class Guard [P <: Proof[_,P]] extends (ProofNodeCollection[P] => Boolean) {
  def &(other: Guard[P]) = new Guard[P] { def apply(r: ProofNodeCollection[P]) = this(r) & other(r) }
}

/* I find it more convenient to implement the default guards as functions and
 * anonymous classes. If you find it ugly it could of course be implemented as
 * classes and objects.
 *
 * If kept as is, I plan to move this functions to package object file
 * algorithm/compressor/guard/package.scala.
 */
object Guard {
  def once[P <: Proof[_,P]]    = new Guard[P] { def apply(r: ProofNodeCollection[P]) = false }
  def forever[P <: Proof[_,P]] = new Guard[P] { def apply(r: ProofNodeCollection[P]) = true }

  /** A time out guard
    *
    * @param howLong duration in miliseconds
    */
  def timeout[P <: Proof[_,P]](howLong: Double) = new Guard[P] {
    val begining = System.nanoTime
    def apply(r: ProofNodeCollection[P]) =
      (System.nanoTime.toDouble - begining) / 1000000 < howLong
  }

  def count[P <: Proof[_,P]](howMany: Long) = new Guard[P] {
    var count = 0
    def apply(r: ProofNodeCollection[P]) = {
      count += 1
      count < howMany
    }
  }
}
