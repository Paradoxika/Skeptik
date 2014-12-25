package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.Proof.apply
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}

trait RandomChoice
extends AbstractSplitHeuristic {
  private val rand = new scala.util.Random()

  private def randomLong(max: Long):Long = {
    if (max <= Int.MaxValue.toLong)
      rand.nextInt(max.toInt)
    else {
      var draw = rand.nextLong()
      if (draw < 0) draw = -draw
      if (draw < max) draw else ((draw - max).toDouble * max.toDouble / (Long.MaxValue - max).toDouble).toLong
    }
  }

  def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long) = {
    val iterator = literalAdditivity.toIterator
    def searchPos(left: Long):E = {
      val next = iterator.next
      if (next._2 < left && iterator.hasNext) searchPos(left - next._2) else next._1
    }
    searchPos(randomLong(totalAdditivity) + 1)
  }
}
