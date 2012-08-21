package at.logic.skeptik.judgment 

import collection.TraversableOnce
import collection.mutable.Stack
import at.logic.skeptik.expression._
import at.logic.skeptik.util.unicode._
import at.logic.skeptik.expression.formula._
import language.reflectiveCalls
import language.implicitConversions


abstract class ASequent extends Judgment {
  implicit private def enrichIterable[T](c: Iterable[T]) = new RichIterable(c)
  private class RichIterable[T](c: Iterable[T]) {
    def contains(e: T) = if (c.isInstanceOf[Seq[_]]) c.asInstanceOf[Seq[T]].contains(e)
                         else if (c.isInstanceOf[Set[_]]) c.asInstanceOf[Set[T]].contains(e)
                         else throw new Exception("unsupported collection")
  }
  
  def ant: Iterable[E]
  def suc: Iterable[E]

  def isFalse = (ant.size == 0) && (suc.size == 0)
  
  def size = ant.size + suc.size + 1
 
  override def equals(v: Any) = v match {    
      case that: ASequent => (that canEqual this) && (ant == that.ant) && (suc == that.suc) 
      case _ => false   
  }   
  def canEqual(other: Any) = other.isInstanceOf[ASequent]
  
  
  def subsequentOf(that: ASequent) = ant.forall(f => that.ant contains f) && suc.forall(f => that.suc contains f)
  
  @deprecated
  def isSubsequentOf(that: ASequent) = ant.forall(f => that.ant contains f) && suc.forall(f => that.suc contains f)
  
  def toSetSequent = new immutable.SetSequent(ant.toSet, suc.toSet)
  
  override def hashCode = 42*ant.hashCode + suc.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
  

}

