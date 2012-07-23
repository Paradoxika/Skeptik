package at.logic.skeptik.judgment 

import collection.TraversableOnce
import collection.immutable.{HashSet => ISet}
import collection.mutable.Stack
import at.logic.skeptik.expression._
import at.logic.skeptik.util.unicode._
import at.logic.skeptik.expression.formula._


abstract class ASequent extends Judgment {
  private type Cedent = {
    def contains(e: E): Boolean
    def size: Int
    def mkString(sep: String): String
  }
  def ant: Cedent
  def suc: Cedent
 
  def contains(f:E) = (ant contains f) || (suc contains f)
  
  def contains(e: Either[E,E]) = e match {
    case Left(f) => ant contains f
    case Right(f) => suc contains f
  }

  def isFalse = (ant.size == 0) && (suc.size == 0)
  
  def size = ant.size + suc.size + 1
 
  override def equals(v:Any) = v match {    
      case that: ASequent => (that canEqual this) && (ant == that.ant) && (suc == that.suc) 
      case _ => false   
  }   
  def canEqual(other: Any) = other.isInstanceOf[ASequent]
  
  override def hashCode = 42*ant.hashCode + suc.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
}

// TODO: (B) Move this class to the immutable package
// TODO: (B) change the type of ant and suc to Seq[E]
class Sequent(val ant:List[E], val suc:List[E]) extends Judgment {
	def contains(f:E) = (ant contains f) || (suc contains f)
	def exists(p:E=>Boolean) = ant.exists(p) || suc.exists(p)
	def supersequentOf(s:Sequent) = s.ant.forall(f => ant contains f) && s.suc.forall(f => suc contains f)
  
  def ++(s:Sequent) = new Sequent(ant ++ s.ant, suc ++ s.suc)
  def +(f:E) = new Sequent(ant, f::suc)
  def +:(f:E) = new Sequent(f::ant, suc)
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
  
  def size = ((ant:::suc).map(_.size) :\ 0)(_ + _ + 1) 
  
  override def hashCode = 42*ant.toSet.hashCode + suc.toSet.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
  def toSet: ISet[E] = ISet() ++ ant.map(f => Neg(f)) ++ suc
}
// ToDo: (B) clean this companion object
object Sequent {
  def apply(ant:E*)(suc:E*) = new Sequent(ant.toList, suc.toList)
  def apply(ant:List[E], suc:List[E]) = new Sequent(ant,suc)
  def apply(ant:List[E], suc:E) = new Sequent(ant,suc::Nil)
  def apply(ant:E, suc:List[E]) = new Sequent(ant::Nil,suc)
  def apply(ant:E, suc:E) = new Sequent(ant::Nil,suc::Nil)
  def apply() = new Sequent(Nil,Nil)
  def apply(s: TraversableOnce[E]) = {
    val ant = new Stack[E]; val suc = new Stack[E];
    for (f <- s) f match {
      case Neg(g) => ant.push(g)
      case _ => suc.push(f)
  }
    new Sequent(ant.toList,suc.toList)
  } 
}


