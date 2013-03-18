package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof._
import language.implicitConversions

package object guard {

  /* Default guard */

  def once[P <: ProofNode[Judgment,P]]    = new Guard[P] { def apply(r: Proof[P]) = false }
  def forever[P <: ProofNode[Judgment,P]] = new Guard[P] { def apply(r: Proof[P]) = true }

  /** A time out guard
    *
    * @param howLong duration in miliseconds
    */
  def timeout[P <: ProofNode[Judgment,P]](howLong: Double) = new Guard[P] {
    val begining = System.nanoTime
    def apply(r: Proof[P]) =
      (System.nanoTime.toDouble - begining) / 1000000 < howLong
  }

  def count[P <: ProofNode[Judgment,P]](howMany: Long) = new Guard[P] {
    var count = 0
    def apply(r: Proof[P]) = {
      count += 1
      count < howMany
    }
  }



  /* Implicit conversions */

  /* (Proof => Boolean) to Guard[ProofNode] */
  implicit def proofFctToGuard[P <: ProofNode[Judgment,P]](fct: Proof[P] => Boolean) = new Guard[P] { def apply(r: Proof[P]) = fct(r) }

  /* (() => Boolean) to Guard[_] */
  implicit def fctToGuard[P <: ProofNode[Judgment,P]](fct: () => Boolean) = new Guard[P] { def apply(r: Proof[P]) = fct() }

}
