package skeptik.expression

import skeptik.judgment.Judgment
import skeptik.util.unicode._
  
sealed abstract class E extends Judgment {
  def t: T
    
  def copy: E
    
  def size: Int
  
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
  // ToDo: maybe substitutions should be moved outside this class. 
  // They should be programmed as an internal DSL, similar to positions. 
  def /(subs: Map[Var,E]) =  {
    def rec(f:E,boundVars:Set[Var]):E = f match {
      case App(e1, e2) => App(rec(e1,boundVars),rec(e2,boundVars))
      case Abs(v,e) => Abs(v.copy, rec(e, boundVars + v))
      case v: Var if (boundVars contains v) => v.copy 
      case v: Var if (subs contains v) => subs(v).copy
      case v: Var => v.copy
    }
    rec(this, Set())
  }
}
case class Var(val name: String, override val t:T) extends E {
  def copy = new Var(name,t)
  def size = 1
  override def toString = name
}
case class Abs(val variable: Var, val body: E) extends E {
  def copy = new Abs(variable.copy,body.copy)
  override lazy val t = variable.t -> body.t 
  def size = (variable.t.size + 1) + body.size + 1
  override def toString = unicodeOrElse("\u03BB","@") + variable.name + ":" + variable.t + "." + body
}
case class App(val function: E, val argument: E) extends E {
  require(function.t.asInstanceOf[arrow].t1 == argument.t)
  def copy = new App(function.copy,argument.copy)
  override lazy val t = function.t.asInstanceOf[arrow].t2
  def size = function.size + argument.size + 1

  override def toString = this match {
    case App(App(s:Var with Infix, a), b) => "(" + a + " " + s + " " + b +  ")"
    case _ => "(" + function + " " + argument + ")"
  }
}

trait Infix extends Var