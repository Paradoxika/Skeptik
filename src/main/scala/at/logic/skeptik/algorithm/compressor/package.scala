package at.logic.skeptik.algorithm

import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.compressor.guard._

package object compressor {

  /** A faster "size" */
  def fakeSize[A](l: List[A]) = l match {
    case Nil => 0
    case _::Nil => 1
    case _::_ => 2
  }

  /* Scala forbids to inherit from different function traits. As a workaround,
   * some implicit conversion are provided.
   */

  /* AbstratcCompressorAlgorithm to (ProofNodeCollection[P] => ProofNodeCollection[P]) */
  implicit def compressorAlgorithmToFunctionProofNodeCollection[P <: Proof[_,P]](a: CompressorAlgorithm[P]) =
    { (p: ProofNodeCollection[P]) => a(p) }

  /* AbstratcCompressorAlgorithm to ((ProofNodeCollection[P], Guard[P]) => ProofNodeCollection[P]) */
  implicit def compressorAlgorithmToFunctionProofNodeCollectionWithGuard[P <: Proof[_,P]](a: CompressorAlgorithm[P]) =
    { (p: ProofNodeCollection[P], g: Guard[P]) => a(p,g) }

}
