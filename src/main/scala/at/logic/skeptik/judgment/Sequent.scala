package at.logic.skeptik.judgment 

import collection.TraversableOnce
import collection.mutable.Stack
import at.logic.skeptik.expression._
import at.logic.skeptik.util.unicode._
import at.logic.skeptik.expression.formula._
import language.reflectiveCalls
import language.implicitConversions

class RichIterable[T](c: Iterable[T]) {
  def contains(e: T) = { 
    if (c.isInstanceOf[Seq[_]]) c.asInstanceOf[Seq[T]].contains(e)
    else if (c.isInstanceOf[Set[_]]) c.asInstanceOf[Set[T]].contains(e)
    else throw new Exception("unsupported collection")
  }
}

object implicits {
  implicit def enrichIterable[T](c: Iterable[T]) = new RichIterable(c)
}
import implicits._


abstract class ASequent extends Judgment {
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
  
  override def hashCode = 42*ant.hashCode + suc.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
}

// TODO: (B) Move this class to the immutable package
// TODO: (B) change the type of ant and suc to Seq[E]
class Sequent(val ant:Seq[E], val suc:Seq[E]) extends Judgment {
	
  def isSubsequentOf(that: Sequent) = ant.forall(f => that.ant contains f) && suc.forall(f => that.suc contains f)
	
	
  def ++(s:Sequent) = new Sequent(ant ++ s.ant, suc ++ s.suc)
  def +(f:E) = new Sequent(ant, suc :+ f)
  def +:(f:E) = new Sequent(f +: ant, suc)
  def -(f:E) = new Sequent(ant, suc.filterNot(_ == f)) 
  def -:(f:E) = new Sequent(ant.filterNot(_ == f), suc) 
	def --(s:Sequent) = new Sequent(ant.filterNot(f => s.ant.exists(_ == f)), suc.filterNot(f => s.suc.exists(_ == f)))
	def -*(f:E) = new Sequent(ant, suc.filterNot(_ eq f)) 
  def -*:(f:E) = new Sequent(ant.filterNot(_ eq f), suc)  
  def --*(s:Sequent) = new Sequent(ant.filterNot(f => s.ant.exists(_ eq f)), suc.filterNot(f => s.suc.exists(_ eq f)))
	
  override def equals(v:Any) = v match {		
      case that:Sequent => (that canEqual this) && (ant.toSet == that.ant.toSet) && (suc.toSet == that.suc.toSet)	
      case _ => false		
  }		
  def canEqual(other: Any) = other.isInstanceOf[Sequent]
  
  def size = ((ant union suc).map(_.size) :\ 0)(_ + _ + 1) 
  
  override def hashCode = 42*ant.toSet.hashCode + suc.toSet.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
}


object Sequent {
  def apply(ant:Iterable[E])(suc:Iterable[E]) = new Sequent(ant.toSeq, suc.toSeq)
  def apply(ant:E*)(suc:E*) = new Sequent(ant, suc)
  def apply(s: TraversableOnce[E]) = {
    val ant = new Stack[E]; val suc = new Stack[E];
    for (f <- s) f match {
      case Neg(g) => ant.push(g)
      case _ => suc.push(f)
    }
    new Sequent(ant,suc)
  } 
}


