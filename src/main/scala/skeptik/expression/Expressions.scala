package skeptik.expression

import scala.collection.immutable.{HashMap => IMap,HashSet => ISet}
import skeptik.judgment.Judgment
 
  
abstract class E extends Judgment {
  def t: T
    
  def copy: E
    
  def =+=(e:E) = alphaEquals(e)
  def alphaEquals(e:E) = {
    def alphaEqualsRec(e1:E,e2:E,map:IMap[Var,Var]): Boolean = (e1,e2) match {
      case (v1:Var, v2:Var) => map.getOrElse(v1,v1)==v2
      case (Abs(v1@Var(_,t1),b1),Abs(v2@Var(_,t2),b2)) => {
        if (v1 == v2) alphaEqualsRec(b1, b2, map)
        else if (t1 == t2) alphaEqualsRec(b1, b2, map.updated(v1,v2))
        else false
      }
      case (App(f1,a1),App(f2,a2)) => alphaEqualsRec(f1, f2, map) && alphaEqualsRec(a1, a2, map)
      case _ => false
    }
    alphaEqualsRec(this, e, new IMap[Var,Var])
  }
  def occursIn(e:E):Boolean = if (this == e) true else e match {
    case v: Var => false
    case App(f,a) => (this occursIn f) || (this occursIn a)
    case Abs(v,g) => (this occursIn v) || (this occursIn g)
  }
  type Sub = Pair[Var,E]
  def /(substitutions: List[Sub]) = applySubstitutions(substitutions) 
  def applySubstitutions(subs: List[Sub]) = {
    val subsMap = IMap(subs.map(s => ((s._1.name,s._1.t) -> s._2)): _*)
    def sRec(f:E,boundVars:ISet[(String,T)]):E = f match {
      case App(e1, e2) => App(sRec(e1,boundVars),sRec(e2,boundVars))
      case Abs(Var(n,t),e) => Abs(Var(n,t), sRec(e, boundVars.+((n,t))))
      case v: Var if (boundVars contains (v.name, v.t)) => v.copy 
      case v: Var if (subsMap contains (v.name, v.t)) => subsMap((v.name, v.t)).copy
      case v: Var => v.copy
    }
    sRec(this, new ISet[(String,T)])
  }
  def stringRep = toString
}
case class Var(val name: String, override val t:T) extends E {
  override def copy = new Var(name,t)
  override def toString = name
}
case class Abs(val variable: Var, val body: E) extends E {
  def copy = new Abs(variable.copy,body.copy)
  override lazy val t = variable.t -> body.t
  override def toString = "@" + variable.name + ":" + variable.t + "." + body
}
case class App(val function: E, val argument: E) extends E {
  require(function.t.asInstanceOf[arrow].t1 == argument.t)
  def copy = new App(function.copy,argument.copy)
  override lazy val t = function.t.asInstanceOf[arrow].t2
  override def toString = "(" + function + " " + argument + ")"
}

