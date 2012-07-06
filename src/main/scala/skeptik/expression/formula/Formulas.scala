package skeptik.expression
package formula

import skeptik.expression.position.{Position,PredicatePosition}

abstract class FormulaConstructorExtractor {
  def unapply(f:E):Option[_]
  def ?:(f: E) = unapply(f).isInstanceOf[Some[_]]
}

abstract class Binary(connective: Var) extends FormulaConstructorExtractor {
  def apply(f1: E, f2: E) = App(App(connective,f1),f2)
  def unapply(e:E) = e match {
    case App(App(c,f1),f2) if c == connective => Some((f1,f2))
    case _ => None
  }  
}

abstract class Unary(connective: Var) extends FormulaConstructorExtractor {
  def apply(f: E) = App(connective,f)
  def unapply(e:E) = e match {
    case App(c,f) if c == connective => Some(f)
    case _ => None
  }  
}

abstract class Q(quantifierC:T=>E) extends FormulaConstructorExtractor {
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


object Neg extends Unary(negC)

object And extends Binary(andC)

object Or extends Binary(andC)

object Imp extends Binary(impC)
  
object All extends Q(allC)  

object Ex extends Q(exC)



object Prop {
  def apply(name: String) = Var(name, o)
  def unapply(e: E) = e match {
    case Var(name,t) if t == o => Some(name)
    case _ => None
  }
}

object Atom {
  def apply(p: E, args: List[E]) = {
    val atom = (p /: args)((p,a) => App(p,a))
    require(atom.t == o)
    atom
  }
  def unapply(e:E) = e match {
    case e: Var if e.t == o => Some((e,Nil))
    case e: App if e.t == o => {
      val r @ (p,args) = unapplyRec(e)
      if (isLogicalConnective(p)) None 
      else Some(r)
    }
    case _ => None
  }
  private def unapplyRec(e: App): (E,List[E]) = e.function match {
    case a : App => {
        val (predicate, firstArgs) = unapplyRec(a)
        return (predicate, firstArgs ::: (e.argument::Nil))
    }
    case _ => return (e.function, e.argument::Nil) 
  } 
}

