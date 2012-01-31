package ResK

import scala.collection.immutable.{HashMap => IMap}
import scala.collection.immutable.{HashSet => ISet}

object expressions {
  abstract class T {
    def ->(t:T) = arrow(this,t)
  }
  case object i extends T
  case object o extends T
  case class arrow(t1:T, t2:T) extends T
 
  type Label = Any
  type LabelMap = IMap[String,Label] 
  object LabelMap {def apply(l:(String,Label)*) = IMap(l:_*)}
  def copyLabels(lM:LabelMap):LabelMap = lM

  trait Copiable[X] {def copy: X with Copiable[X]}
  
  abstract class E extends Copiable[E] {
    def t: T
    def labels : LabelMap
    def =*=(e:E) = syntaticEquals(e)
    def syntaticEquals(e:E):Boolean = (this,e) match {
      case (Var(n1,t1),Var(n2,t2)) if (n1==n2 && t1 == t2) => true
      case (Abs(v1,b1),Abs(v2,b2)) => (v1 syntaticEquals v2) && (b1 syntaticEquals b2)
      case (App(f1,a1),App(f2,a2)) => (f1 syntaticEquals f2) && (a1 syntaticEquals a2)
      case _ => false
    }
    def =+=(e:E) = alphaEquals(e)
    def alphaEquals(e:E) = {
      //ToDo: fix bug
      def alphaEqualsRec(e1:E,e2:E,map:IMap[(String,T),(String,T)]): Boolean = (e1,e2) match {
        case (Var(n1,t1),Var(n2,t2)) => if (n1==n2 && t1 == t2) true
                                        else if (map((n1,t1))==(n2, t2)) true
                                        else false
        case (Abs(v1,b1),Abs(v2,b2)) => {
          if (v1 syntaticEquals v2) alphaEqualsRec(b1, b2, map)
          else if (v1.t == v2.t) {
            val newMap = if (map contains v1.p) (map.-(v1.p)) + (v1.p -> v2.p)
                         else map + (v1.p -> v2.p)
            alphaEqualsRec(b1, b2, newMap)
          }
          else false
        }
        case (App(f1,a1),App(f2,a2)) => alphaEqualsRec(f1, f2, map) && alphaEqualsRec(a1, a2, map)
        case _ => false
      }
      alphaEqualsRec(this, e, new IMap[(String,T),(String,T)])
    }
    def occursIn(e:E):Boolean = if (this syntaticEquals e) true else e match {
      case v: Var => false
      case App(f,a) => (this occursIn f) || (this occursIn a)
      case Abs(v,g) => (this occursIn v) || (this occursIn g)
    }
    def /(substitutions: List[Sub]) = applySubstitutions(substitutions) 
    def applySubstitutions(substitutions: List[Sub]) = {
      val subs = IMap(substitutions.map(s => (s._1.p -> s._2)): _*)
      def sRec(f:E,boundVars:ISet[(String,T)]):E = f match {
        case App(e1, e2) => App(sRec(e1,boundVars),sRec(e2,boundVars))
        case Abs(x,e) => Abs(x.copy, sRec(e,boundVars + x.p))
        case v: Var if (boundVars contains v.p) => v.copy 
        case v: Var if (subs contains v.p) => subs(v.p).copy
        case v: Var => v.copy
      }
      sRec(this, new ISet[(String,T)])
    }
  }
  class Var(val name: String, override val t:T, val labels: LabelMap) extends E {
    override def copy = new Var(name,t,copyLabels(labels))
    override def toString = name
    def p = (name,t)
  }
  class Abs(val variable: Var, val body: E, val labels: LabelMap) extends E {
    def copy = new Abs(variable.copy,body.copy,copyLabels(labels))
    override lazy val t = variable.t -> body.t
    override def toString = "@" + variable.name + ":" + variable.t + "." + body
  }
  class App(val function: E, val argument: E, val labels: LabelMap) extends E {
    require(function.t.asInstanceOf[arrow].t1 == argument.t)
    def copy = new App(function.copy,argument.copy,copyLabels(labels))
    override lazy val t = function.t.asInstanceOf[arrow].t2
    override def toString = "(" + function + " " + argument + ")"
  }

  object Var {
    def apply(name: String, t:T) = new Var(name, t, null)
    def apply(name: String, t:T, labels: LabelMap) = new Var(name, t, labels)
    def apply(name: String, t:T, label: String) = new Var(name, t, LabelMap((label -> true)))
    def unapply(e: E) = e match {
      case e: Var => Some((e.name,e.t))
      case _ => None
    }
  }
  object Abs {
    def apply(variable: Var, body: E) = new Abs(variable, body, null)
    def apply(variable: Var, body: E, labels: LabelMap) = new Abs(variable, body, labels)
    def unapply(e: E) = e match {
      case e: Abs => Some((e.variable,e.body))
      case _ => None
    }
  }
  object App {
    def apply(function: E, argument: E) = new App(function,argument, null)
    def apply(function: E, argument: E, labels: LabelMap) = new App(function,argument, labels)
    def unapply(e: E) = e match {
      case e: App => Some((e.function,e.argument))
      case _ => None
    }
  }   


  type Sub = Pair[Var,E]
  
  object algorithms {
    def unify(equations:List[(E,E)]): Option[List[Sub]] = {
      var eqs = equations
      var unifier: List[Sub] = Nil
      def isEigen(v:Var): Boolean = if (v.labels != null) v.labels("eigen") == true else false 
      while (eqs != Nil) {
        eqs.head match {
          case (App(f1,a1),App(f2,a2)) => eqs = (f1,f2)::(a1,a2)::eqs.tail
          case (Abs(v1,e1),Abs(v2,e2)) => eqs = (v1,v2)::(e1,e2)::eqs.tail
          case (v:Var,e:E) if isEigen(v) => {
              unifier = (v -> e)::unifier 
              eqs = eqs.tail
          }
          case (e:E,v:Var) if isEigen(v) => {
              unifier = (v -> e)::unifier 
              eqs = eqs.tail
          }
          case (v1:Var,v2:Var) if (v1 =*= v2) => eqs = eqs.tail    
          case _ => return None
        }
      }
      
      val clash: Boolean = unifier.exists(s1 => {
                            unifier.exists(s2 => {
                                ((s1._1 =*= s2._1) && 
                                 !(s1._2 =*= s2._2))    
                            })
                          })
                         
      if (clash) None else Some(unifier)
    }
  }
  

}