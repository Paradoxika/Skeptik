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

}
