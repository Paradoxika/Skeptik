package skeptik.expression
package formula
package position

import scala.collection.mutable.{HashMap => MMap}

  
abstract class Position {
  // returns the subformula of f at this position
  def !:(f:E):E
  
  // applies f at this position in formula
  def @:(f: E => E)(formula: E): E
  
  def isPositiveIn(formula: E): Boolean
  
  def getSubpositions(formula: E) : Seq[Position]
}

//package object deprecated {
//  @deprecated
//  type IntListPosition = List[Int] // ToDo: refactor this into a subclass of Position, if needed. Maybe it is better to try to use SubformulaP instead.
//}
class InexistentPositionException(formula: E, position: Position) extends Exception("Position " + position + " does not exist in formula " + formula)

class EmptyP() extends IntListP(Nil)

class SubformulaP(subformula: E, override val index: Int) extends PredicateP(_ == subformula, index)

case class IntListP(list: List[Int]) extends Position {
  def !:(formula:E):E = {
    (list, formula) match {
      case (0::t,Imp(a,b)) => b !: IntListP(t)
      case (1::t,Imp(a,b)) => a !: IntListP(t)
      case (Nil,f) => f
      case _ => throw new InexistentPositionException(formula,this)
    }
  }  
  
  def getSubpositions(formula: E) : Seq[IntListP] = {  
    def rec(e: E):Seq[List[Int]] = e match {
      case v @ Prop(name) => Seq(Nil)
      case i @ Imp(a,b) => Seq(Nil) ++ rec(a).map(1::_) ++ rec(b).map(0::_)
    }
    rec(formula).map(l => IntListP(this.list ::: l))
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
  
  def existsIn(formula: E): Boolean = {
    try {
      formula !: this
      true
    } catch {
      case e: InexistentPositionException => false
    }
  }
  
  def isPositiveIn(formula: E): Boolean = {
    (list, formula) match {
      case (0::t,Imp(a,b)) => IntListP(t) isPositiveIn b
      case (1::t,Imp(a,b)) => ! (IntListP(t) isPositiveIn a)
      case (Nil,f) => true
      case _ => throw new InexistentPositionException(formula,this)
    }
  }
}


// position of the index-th occurrence of subformula
case class PredicateP(isSearchedSubformula: E => Boolean, index: Int) extends Position {
  def !:(formula:E):E = {
    var count = 0
    def rec(e: E): Option[E] = {
      def propagateResult[A](r1:Option[A],r2:Option[A]) = (r1,r2) match {
        case (Some(b),None) => Some(b)
        case (None,Some(b)) => Some(b)
        case (None,None) => None
        case (Some(b1),Some(b2)) => throw new Exception("this case should never occur.")
      }
      if (isSearchedSubformula(e)) count += 1
      if (isSearchedSubformula(e) && count == index) Some(e)
      else e match {
        case v: Var => None
        case App(g,a) => propagateResult(rec(g),rec(a))
        case Abs(v,g) => propagateResult(rec(v),rec(g))
      }
    } 
    rec(formula).getOrElse(throw new InexistentPositionException(formula,this))
  }
  
  
  // I think this is buggy.
  def getSubpositions(formula: E) : Seq[PredicateP] = {
    val counter = new MMap[E,Int]
    def getPositionOf(e:E) = {
      counter.update(e, counter.getOrElse(e,0)+1)
      PredicateP(_ == e, counter(e))
    }      
    def rec(e: E):Seq[PredicateP] = e match {
      case v @ Prop(name) => Seq(getPositionOf(v))
      case i @ Imp(a,b) => Seq(getPositionOf(i)) ++ rec(a) ++ rec(b)
    }
    rec(formula)
  }
  
  def @:(f: E => E)(formula:E): E = {
    var count = 0
    def rec(e: E): E = {
      if (isSearchedSubformula(e)) count += 1
      if (isSearchedSubformula(e) && count == index) f(e)
      else e match {
        case v: Var => v
        case App(g,a) => App(rec(g),rec(a))
        case Abs(v,g) => Abs(rec(v).asInstanceOf[Var],rec(g))
      }     
    } 
    val result = rec(formula)
    if (count >= index) result 
    else throw new InexistentPositionException(formula,this)
  }
  
  def existsIn(formula: E): Boolean = {
    try {
      formula !: this
      true
    } catch {
      case e: InexistentPositionException => false
    }
  }
  
  def isPositiveIn(formula: E): Boolean = {
    var count = 0 
    def rec(e:E): Option[Boolean] = {
      if (isSearchedSubformula(e)) count += 1
      
      def propagateResult(r1:Option[Boolean],r2:Option[Boolean]) = (r1,r2) match {
        case (Some(b),None) => Some(b)
        case (None,Some(b)) => Some(b)
        case (None,None) => None
        case (Some(b1),Some(b2)) => throw new Exception("this case should never occur.")
      }
      
      if (isSearchedSubformula(e) && count == index) Some(true)
      else e match {
        case Imp(a,b) => (rec(a),rec(b)) match {
          case (Some(b),None) => Some(!b)
          case (r1,r2) => propagateResult(r1,r2) 
        }
        case App(g,a) => propagateResult(rec(g),rec(a))
        case Abs(v,g) => propagateResult(rec(v),rec(g))
        case v: Var => None
      }
    }
    rec(formula).getOrElse(throw new InexistentPositionException(formula,this))
  }
}