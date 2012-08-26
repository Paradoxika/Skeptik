package at.logic.skeptik.judgment 

import at.logic.skeptik.expression.E
import at.logic.skeptik.util.unicode._

import collection.IterableLike
import collection.mutable.{Builder, MapBuilder}
import collection.generic.CanBuildFrom

trait Sequent extends Judgment with SequentLike[Sequent] {

  def toSetSequent = new immutable.SetSequent(ant.toSet, suc.toSet)
  def toSeqSequent = new immutable.SeqSequent(ant.toSeq, suc.toSeq)
  
  override def equals(v: Any) = v match {    
      case that: Sequent => (that canEqual this) && (ant == that.ant) && (suc == that.suc) 
      case _ => false   
  }   
  def canEqual(other: Any) = other.isInstanceOf[Sequent]  
  override def hashCode = 42*ant.hashCode + suc.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
}