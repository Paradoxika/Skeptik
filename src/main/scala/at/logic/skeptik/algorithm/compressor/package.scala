package at.logic.skeptik.algorithm

import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.compressor.guard._
import language.implicitConversions

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

  /* AbstratcProofCompressor to (Proof[P] => Proof[P]) */
  implicit def compressorAlgorithmToFunctionProof[P <: ProofNode[Judgment,P]](a: ProofCompressor[P]) =
    { (p: Proof[P]) => a(p) }

  /* AbstratcProofCompressor to ((Proof[P], Guard[P]) => Proof[P]) */
  implicit def compressorAlgorithmToFunctionProofWithGuard[P <: ProofNode[Judgment,P]](a: ProofCompressor[P]) =
    { (p: Proof[P], g: Guard[P]) => a(p,g) }

}
