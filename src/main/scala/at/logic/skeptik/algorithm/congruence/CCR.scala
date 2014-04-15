package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.{HashSet => MSet}
import scala.collection.immutable.{HashSet => ISet}

class CCR(val initTerm: E, val s: E, val term: Set[E], val pred: Set[E], val rightNeighbours: Set[E]) {
//  var s: E = initTerm
//  val term: ListBuffer[E] = ListBuffer(initTerm)
//  val pred: ListBuffer[E] = ListBuffer()
  
  def this(initTerm: E) = this(initTerm, initTerm, Set(initTerm), Set[E](), Set[E]())
  
//  term.+=(initTerm)
  
  override def toString: String = "["+s.toString+"]"
}

//object DummyCCR extends CCR