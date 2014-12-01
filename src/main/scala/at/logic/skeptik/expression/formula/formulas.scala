package at.logic.skeptik.expression
package formula

import at.logic.skeptik.expression.position.{Position,PredicatePosition}

abstract class Formula {
  def unapply(f:E):Option[_]
  def ?:(f: E) = unapply(f).isInstanceOf[Some[_]]
}

abstract class BinaryFormula(connective: Var) extends Formula {
  def apply(f1: E, f2: E) = App(App(connective,f1),f2)
  def unapply(e:E) = e match {
    case App(App(c,f1),f2) if c == connective => Some((f1,f2))
    case _ => None
  }  
}

abstract class UnaryFormula(connective: Var) extends Formula {
  def apply(f: E) = App(connective,f)
  def unapply(e:E) = e match {
    case App(c,f) if c == connective => Some(f)
    case _ => None
  }  
}

abstract class QuantifierFormula(quantifierC:T=>E) extends Formula {
  def apply(v:Var, f:E) = App(quantifierC(v.t), Abs(v,f))
  def apply(f:E, v:Var, p:Position) = {
    val h = (( (_:E) => v.copy) @: p)(f)
    App(quantifierC(v.t), Abs(v,h))
  }
  def apply(f:E, v:Var, t:E): E = apply(f, v, new PredicatePosition(_ == t)) 
    
  def unapply(e:E) = e match {
    case App(q, Abs(v,f)) if q == quantifierC(v.t) => Some((v,f))
    case _ => None
  }  
}


object Neg extends UnaryFormula(negC)

object And extends BinaryFormula(andC)

object Or extends BinaryFormula(orC)

object Imp extends BinaryFormula(impC)
  
object All extends QuantifierFormula(allC)  

object Ex extends QuantifierFormula(exC)

object Atom extends Formula {
  def apply(p: E, args: List[E]) = {
    val atom = AppRec(p,args)
    require(atom.t == o)
    atom
  }
  def unapply(e:E) = e match {
    case AppRec(f,args) if (e.t == o && !isLogicalConnective(f)) => Some((f,args))
    case _ => None
  }
}

