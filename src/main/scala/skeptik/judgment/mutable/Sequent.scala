package skeptik.judgment.mutable
import skeptik.judgment.Judgment


import skeptik.expression.E
import skeptik.util.unicode._
  
// Cedent is a type class
trait Cedent[Coll] {
  def add(c: Coll, e: E): Unit
  def remove(c: Coll, e: E): Unit
  def contains(c: Coll, e: E): Boolean
  def toList(c: Coll): List[E]
  def size(c: Coll): Int
}

class Sequent[C : Cedent](val ant:C, val suc:C) extends Judgment {
  private val cedent = implicitly[Cedent[C]]
  
  def contains(f:E) = cedent.contains(ant, f) || cedent.contains(suc, f)
  
  def +=(f:E) = cedent.add(suc, f)
  def =+:(f:E) = cedent.add(ant, f)
  def -=(f:E) = cedent.remove(suc, f)
  def =-:(f:E) = cedent.remove(ant, f)
  
  override def equals(v:Any) = v match {    
      case that:Sequent[C] => (that canEqual this) && (ant == that.ant) && (suc == that.suc) 
      case _ => false   
  }   
  def canEqual(other: Any) = other.isInstanceOf[Sequent[C]]
  
  def size = cedent.size(ant) + cedent.size(suc) + 1
  
  override def hashCode = 42*ant.hashCode + suc.hashCode
  override def toString = cedent.toList(ant).mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + cedent.toList(suc).mkString(", ")
}



