package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => Map}

class FindTable extends Map[E,CCR] {
  def query(x: E) = this.getOrElseUpdate(x,new CCR(x))
  
}