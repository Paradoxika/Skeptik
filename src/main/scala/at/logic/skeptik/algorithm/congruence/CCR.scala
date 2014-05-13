package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.{HashSet => MSet}
import scala.collection.immutable.{HashSet => ISet}

/**
 * Class CCR
 * is immutable
 * stands for congruence class record - as in Pascal Fontaine's PhD Thesis.
 * represents one congruence class
 * 
 * @param initterm         initial term of the CCR
 * @param s                representative of the CCR (not yet used really)
 * @param term             set of terms in this congruence class
 * @param pred             set of terms where some term in this congruence class is an argument
 * @param rightNeighbours  forgot what I used that for, probably can be removed
 */
class CCR(val initTerm: E, val s: E, val term: Set[E], val pred: Set[E], val rightNeighbours: Set[E]) {

  
  def this(initTerm: E) = this(initTerm, initTerm, Set(initTerm), Set[E](), Set[E]())
  
  override def toString: String = "["+s.toString+"]" + "{"+term+"}"
}
