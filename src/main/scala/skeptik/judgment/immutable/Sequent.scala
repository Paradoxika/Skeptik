package skeptik.judgment
package immutable

import skeptik.expression.E
import skeptik.util.unicode._
  

class SetSequent(val ant: Set[E], val suc: Set[E]) extends Judgment {
  
  def contains(f:E) = (ant contains f) || (suc contains f)
  
  def contains(e: Either[E,E]) = e match {
    case Left(f) => ant contains f
    case Right(f) => suc contains f
  }
  
  def +(f:E) = new SetSequent(ant, suc + f)
  def +:(f:E) = new SetSequent(ant + f, suc)
  def -=(f:E) =  new SetSequent(ant, suc - f)
  def =-:(f:E) = new SetSequent(ant - f, suc)
  
  def +(e: Either[E,E]): SetSequent = e match {
    case Left(f) => +:(f)
    case Right(f) => this.+(f)
  }
  
  override def equals(v:Any) = v match {    
      case that:SetSequent => (that canEqual this) && (ant == that.ant) && (suc == that.suc) 
      case _ => false   
  }   
  def canEqual(other: Any) = other.isInstanceOf[SetSequent]
  
  def size = ant.size + suc.size + 1
  
  override def hashCode = 42*ant.hashCode + suc.hashCode
  override def toString = ant.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + suc.mkString(", ")
}



