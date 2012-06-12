package skeptik.judgment 

import scala.collection.TraversableOnce
import scala.collection.immutable.{HashSet => ISet}
import scala.collection.mutable.Stack
import skeptik.expression._
import skeptik.util.prettyPrinting._
import skeptik.expression.formula._
  

class Sequent(val ant:List[E], val suc:List[E]) extends Judgment {
	def contains(f:E) = (ant contains f) || (suc contains f)
	def exists(p:E=>Boolean) = ant.exists(p) || suc.exists(p)
	def supersequentOf(s:Sequent) = s.ant.forall(f => ant contains f) && s.suc.forall(f => suc contains f)
  def --(s:Sequent) = new Sequent(ant.filterNot(f => s.ant.exists(_ == f)), suc.filterNot(f => s.suc.exists(_ == f)))
  def ++(s:Sequent) = new Sequent(ant ++ s.ant, suc ++ s.suc)
  def +(f:E) = new Sequent(ant, f::suc)
  def +:(f:E) = new Sequent(f::ant, suc)
  def -(f:E) = new Sequent(ant, suc.filterNot(_ == f)) 
  def -:(f:E) = new Sequent(ant.filterNot(_ == f), suc)    
  
  override def equals(v:Any) = v match {		
      case that:Sequent => (that canEqual this) && (ant.toSet == that.ant.toSet) && (suc.toSet == that.suc.toSet)	
      case _ => false		
  }		
  def canEqual(other: Any) = other.isInstanceOf[Sequent]
  
  override def hashCode = 42*ant.toSet.hashCode + suc.toSet.hashCode
  override def toString = listToCSVString(ant) + " :- " + listToCSVString(suc)
  def toSet: ISet[E] = ISet() ++ ant.map(f => Neg(f)) ++ suc
}
object Sequent {
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


