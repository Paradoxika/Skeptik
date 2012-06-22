package skeptik.judgment 

import scala.collection.TraversableOnce
import scala.collection.immutable.{HashSet => ISet}
import scala.collection.mutable.Stack
import skeptik.expression._
import skeptik.util.prettyPrinting._
import skeptik.util.unicode._
import skeptik.expression.formula._
  

case class NamedE(name:String, expression:E) {
  def size = expression.size + 1
  override def toString = name + ": " + expression
}

class NaturalSequent(val context:Set[NamedE], val e:E) extends Judgment {
	
  override def equals(v:Any) = v match {		
      case that:NaturalSequent => (that canEqual this) && (context == that.context) && (e == that.e)	
      case _ => false		
  }		
  def canEqual(other: Any) = other.isInstanceOf[NaturalSequent]
  
  //def size = (context.map(_.size) :\ 0)(_ + _ + 1) + e.size
  def size = e.size
  
  override def hashCode = 42*context.hashCode + e.hashCode
  override def toString = csv(context) + unicodeOrElse(" \u22A2 "," :- ") + e
}


