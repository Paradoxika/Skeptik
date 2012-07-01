package skeptik.judgment
package mutable

import collection.mutable.{Set => MSet}
import skeptik.expression.E
import skeptik.util.unicode._
  

class SetSequent(val ant:MSet[E], val suc:MSet[E]) extends Judgment {
  
  def contains(f:E) = (ant contains f) || (suc contains f)
  
  def +=(f:E) = { suc += f ; this }
  def =+:(f:E) = { ant += f ; this }
  def -=(f:E) =  { suc -= f ; this }
  def =-:(f:E) = { ant -= f ; this }
  
  def +=(e: Either[E,E]): SetSequent = e match {
    case Left(f) => =+:(f)
    case Right(f) => +=(f)
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



