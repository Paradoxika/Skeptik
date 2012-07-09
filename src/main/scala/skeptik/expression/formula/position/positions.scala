package skeptik.expression
package formula
package position

import skeptik.expression.position.{SinglePosition => Position, InexistentPositionException}

object EmptyP extends IntListPosition(Nil)

class IntListPosition(list: List[Int]) extends Position {
  def !:(formula:E): Option[E] = {
    (list, formula) match {
      case (0::t,Imp(a,b)) => b !: new IntListPosition(t)
      case (1::t,Imp(a,b)) => a !: new IntListPosition(t)
      case (Nil,f) => Some(f)
      case _ => None
    }
  }  
  
  override def getSubpositions(formula: E) : Seq[IntListPosition] = {  
    def rec(e: E):Seq[List[Int]] = e match {
      case v @ Var(name,t) => Seq(Nil)
      case i @ Imp(a,b) => Seq(Nil) ++ rec(a).map(1::_) ++ rec(b).map(0::_)
    }
    rec(formula).map(l => new IntListPosition(this.list ::: l))
  }
  
  def @:(f: E => E)(formula:E): E = {
    def rec(e: E, l: List[Int]): E = (e,l) match {
        case (_,Nil) => f(e) 
        case (Imp(a,b),0::t) => Imp(a,rec(b,t))
        case (Imp(a,b),1::t) => Imp(rec(a,t),b)
        case _ => throw new InexistentPositionException(formula,this)
    }     
    rec(formula, this.list)
  }
  
  def isPositiveIn(formula: E): Boolean = {
    (list, formula) match {
      case (0::t,Imp(a,b)) => new IntListPosition(t) isPositiveIn b
      case (1::t,Imp(a,b)) => ! (new IntListPosition(t) isPositiveIn a)
      case (Nil,f) => true
      case _ => throw new InexistentPositionException(formula,this)
    }
  }
}