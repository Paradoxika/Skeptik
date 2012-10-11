package at.logic.skeptik.algorithm

import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.compressor.guard._

package object compressor {

  /** A faster "size" */
  def fakeSize[A](l: Seq[A]) = l.toList match {
    case Nil => 0
    case _::Nil => 1
    case _::_ => 2
  }

  /* Scala forbids to inherit from different function traits. As a workaround,
   * some implicit conversion are provided.
   */

  /* AbstratcCompressorAlgorithm to (Proof[P] => Proof[P]) */
  implicit def compressorAlgorithmToFunctionProof[P <: ProofNode[_,P]](a: CompressorAlgorithm[P]) =
    { (p: Proof[P]) => a(p) }

  /* AbstratcCompressorAlgorithm to ((Proof[P], Guard[P]) => Proof[P]) */
  implicit def compressorAlgorithmToFunctionProofWithGuard[P <: ProofNode[_,P]](a: CompressorAlgorithm[P]) =
    { (p: Proof[P], g: Guard[P]) => a(p,g) }

}
