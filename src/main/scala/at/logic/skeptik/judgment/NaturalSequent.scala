package at.logic.skeptik.judgment 

import at.logic.skeptik.expression._
import at.logic.skeptik.util.unicode._
  

case class NamedE(name:String, expression:E) {
  def logicalSize = expression.logicalSize + 1
  override def toString = name + ": " + expression
}

class NaturalSequent(val context: Set[NamedE], val e:E) extends Judgment {
	
  override def equals(v:Any) = v match {		
      case that:NaturalSequent => (that canEqual this) && (context == that.context) && (e == that.e)	
      case _ => false		
  }		
  def canEqual(other: Any) = other.isInstanceOf[NaturalSequent]
  
  //def logicalSize = (context.map(_.size) :\ 0)(_ + _ + 1) + e.size
  def logicalSize = e.logicalSize
  
  override def hashCode = 42*context.hashCode + e.hashCode
  override def toString = context.mkString(", ") + unicodeOrElse(" \u22A2 "," :- ") + e
}


