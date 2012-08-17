package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof._

package object guard {

  /* Default guard */

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



  /* Implicit conversions */

  /* (ProofNodeCollection => Boolean) to Guard[Proof] */
  implicit def proofFctToGuard[P <: Proof[_,P]](fct: ProofNodeCollection[P] => Boolean) = new Guard[P] { def apply(r: ProofNodeCollection[P]) = fct(r) }

  /* (() => Boolean) to Guard[_] */
  implicit def fctToGuard[P <: Proof[_,P]](fct: () => Boolean) = new Guard[P] { def apply(r: ProofNodeCollection[P]) = fct() }

}
