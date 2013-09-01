package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.expression.E



trait DeterministicChoice 
extends AbstractSplitHeuristic {
  def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long) = {
    val iterator = literalAdditivity.toIterator
    var (result, max) = iterator.next
    var left = totalAdditivity - max
    while (max < left) {
      val next = iterator.next
      if (next._2 > max) {
        result = next._1
        max = next._2
      }
      left -= next._2
    }
    result
  }
}

