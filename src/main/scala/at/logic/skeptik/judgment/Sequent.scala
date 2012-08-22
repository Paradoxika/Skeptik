package at.logic.skeptik.judgment 


import at.logic.skeptik.expression.E
import at.logic.skeptik.util.unicode._
import at.logic.skeptik.util.rich.RichIterable._
import language.reflectiveCalls
import language.implicitConversions

import collection.IterableLike
import collection.mutable.{Builder, MapBuilder}
import collection.generic.CanBuildFrom


trait ISLike[+Repr] {
  def +(f:E): Repr
  def +:(f:E): Repr
  def -(f:E): Repr
  def -:(f:E): Repr
} 

trait MSLike[+Repr] {
  def +=(f:E): Repr
  def =+:(f:E): Repr
  def -=(f:E): Repr
  def =-:(f:E): Repr
}

import at.logic.skeptik.expression.formula.Neg
class SBuilder[Coll <: S] extends Builder[E, Coll] {
  var ant: List[E] = Nil
  var suc: List[E] = Nil
  
  def +=(elem: E) = {
    elem match {
      case Neg(f) => ant = f::ant
      case f => suc = f::suc
    } 
    this
  }
  def clear() = {ant = Nil; suc = Nil}
  def result() = new S(ant, suc).asInstanceOf[Coll]
}

class S(val ant: Iterable[E], val suc: Iterable[E]) extends Iterable[E] with ISLike[S] {
  def +(f:E) = new S(ant, suc ++ Seq(f))
  def +:(f:E) = new S(ant ++ Seq(f), suc)
  def -(f:E) =  new S(ant, suc.filterNot(_ == f))
  def -:(f:E) = new S(ant.filterNot(_ == f), suc)
  
  def iterator = new Iterator[E] {
    val antI = ant.iterator
    val sucI = suc.iterator
    def hasNext = antI.hasNext || sucI.hasNext
    def next() = if (antI.hasNext) Neg(antI.next()) else sucI.next()
  }
} 
object S {
  def empty = new S(Seq(), Seq())
  def apply(ant: Seq[E])(suc: Seq[E]) = new S(ant, suc)
  
  def newBuilder: Builder[E, S] = new SBuilder[S]
  
  implicit def canBuildFrom: CanBuildFrom[S, E, S] = 
      new CanBuildFrom[S, E, S] {
        def apply(from: S) = newBuilder
        def apply() = newBuilder
      }
}


abstract class ASequent extends Judgment {
  def ant: Iterable[E]
  def suc: Iterable[E]
  
  def size = ant.size + suc.size + 1

  def logicalSize = ((ant ++ suc).map(_.logicalSize) :\ 0)(_ + _ + 1) 
  
  def subsequentOf(that: ASequent) = ant.forall(f => that.ant contains f) && suc.forall(f => that.suc contains f)
  
  def isTautological = ant.exists(f => suc contains f)
  
  def toSetSequent = new immutable.SetSequent(ant.toSet, suc.toSet)
  def toSeqSequent = new immutable.SeqSequent(ant.toSeq, suc.toSeq)
  
  override def equals(v: Any) = v match {    
      case that: ASequent => (that canEqual this) && (ant == that.ant) && (suc == that.suc) 
      case _ => false   
  }   
  def canEqual(other: Any) = other.isInstanceOf[ASequent]  
  override def hashCode = 42*ant.hashCode + suc.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
}

