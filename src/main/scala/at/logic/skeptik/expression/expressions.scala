package at.logic.skeptik.expression

import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.util.unicode._
  
sealed abstract class E extends Judgment {
  def t: T
    
  def copy: E
    
  def logicalSize: Int
  
  //alphaEquals
  def =+=(that:E) = {
    def rec(e1:E,e2:E,map:Map[Var,Var]): Boolean = (e1,e2) match {
      case (v1:Var, v2:Var) => map.getOrElse(v1,v1)==v2
      case (Abs(v1@Var(_,t1),b1),Abs(v2@Var(_,t2),b2)) => {
        if (v1 == v2) rec(b1, b2, map)
        else if (t1 == t2) rec(b1, b2, map.updated(v1,v2))
        else false
      }
      case (App(f1,a1),App(f2,a2)) => rec(f1, f2, map) && rec(a1, a2, map)
      case _ => false
    }
    rec(this, that, Map())
  }
  def occursIn(e:E):Boolean = if (this == e) true else e match {
    case v: Var => false
    case App(f,a) => (this occursIn f) || (this occursIn a)
    case Abs(v,g) => (this occursIn v) || (this occursIn g)
  }
}
case class Var(val name: String, override val t:T) extends E {
  def copy = new Var(name,t)
  def logicalSize = 1
  override def toString = name
}
case class Abs(val variable: Var, val body: E) extends E {
  def copy = new Abs(variable.copy,body.copy)
  override lazy val t = variable.t -> body.t 
  def logicalSize = (variable.t.logicalSize + 1) + body.logicalSize + 1
  override def toString = unicodeOrElse("\u03BB","@") + variable.name + ":" + variable.t + "." + body
}
case class App(val function: E, val argument: E) extends E {
  require(function.t.asInstanceOf[Arrow].t1 == argument.t)
  def copy = new App(function.copy,argument.copy)
  override lazy val t = function.t.asInstanceOf[Arrow].t2
  def logicalSize = function.logicalSize + argument.logicalSize + 1
  override def toString = this match {
    case App(App(s:Var with Infix, a), b) => "(" + a + " " + s + " " + b +  ")"
    case AppRec(f, args) => "(" + f + " " + args.mkString(" ") + ")"
  } 
}

object AppRec {
  def apply(p: E, args: Iterable[E]) = (p /: args)((p,a) => App(p,a))
  def unapply(e:E) = e match {
    case e: Var => Some((e,Nil))
    case e: App => Some(unapplyRec(e))
    case _ => None
  }
  private def unapplyRec(e: App): (E,Iterable[E]) = e.function match {
    case a : App => {
        val (function, firstArgs) = unapplyRec(a)
        return (function, firstArgs ++ (e.argument::Nil))
    }
    case _ => return (e.function, e.argument::Nil) 
  } 
}



trait Infix extends Var