package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import scala.collection.mutable.ListBuffer

class CCR(initTerm: E) {
  var s: E = initTerm
  val term: ListBuffer[E] = ListBuffer(initTerm)
  val pred: ListBuffer[E] = ListBuffer()
  
  override def toString: String = "["+initTerm.toString+"]"
}

//object DummyCCR extends CCR