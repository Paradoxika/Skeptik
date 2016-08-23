package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.expression.E
import at.logic.skeptik.expression.formula.Atom

/**
  * Tha trait FORandomChoice implement a random choice for the
  * literals to use to split the proof.
  */
trait FORandomChoice extends AbstractFOSplitHeuristic {
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

  def chooseVariable(literalAdditivity: collection.Map[String,Long], totalAdditivity: Long) = {
    val iterator = literalAdditivity.toIterator
    def searchPos(left: Long): Option[E] = {
      if(iterator.isEmpty) None
      else {
        val next = iterator.next
        if (next._2 < left && iterator.hasNext) searchPos(left - next._2) else Some(Atom(next._1, Nil))
      }
    }
    searchPos(randomLong(totalAdditivity) + 1)
  }
}

trait FOHighestAdditivityChoice {
  def chooseVariable(literalAdditivity: collection.Map[String,Long], totalAdditivity: Long) = {
    def maxAdd(literal1: (String,Long), literal2 : (String,Long)) : (String,Long) =
      if(literal1._2 > literal2._2) literal1 else literal2
    val iterator = literalAdditivity.toIterator
    if(iterator.isEmpty) None
    else Some(Atom(iterator.reduceLeft(maxAdd)._1,Nil))
  }
}
