package ResK

import scala.collection.immutable.{HashMap => IMap}
import scala.collection.immutable.{HashSet => ISet}

object expressions {
  sealed abstract class T {
    def ->(t:T) = arrow(this,t)
  }
  case object i extends T
  case object o extends T
  final case class arrow(t1:T, t2:T) extends T {
    override def toString = "(" + t1 + "->" + t2 + ")"
  }
 
  
  abstract class E {
    def t: T
    
    def copy: E
    
    def =+=(e:E) = alphaEquals(e)
    def alphaEquals(e:E) = {
      def alphaEqualsRec(e1:E,e2:E,map:IMap[Var,Var]): Boolean = (e1,e2) match {
        case (v1:Var, v2:Var) => if (map contains v1) (map(v1)==v2) // renamed bound variables
                                 else (v1 == v2)  // homonymous bound variables or free variables
        case (Abs(v1@Var(_,t1),b1),Abs(v2@Var(_,t2),b2)) => {
          if (v1 == v2) alphaEqualsRec(b1, b2, map)
          else if (t1 == t2) {
            val newMap = if (map contains v1) (map - v1) + (v1 -> v2)  // ToDo: improve this line
                         else map + (v1 -> v2)
            alphaEqualsRec(b1, b2, newMap)
          }
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


  type Sub = Pair[Var,E]
  
  object algorithms {
    
    // ToDo: this is an ad-hoc unification algorithm.
    def unify(equations: List[(E,E)])(implicit unifiableVariables: Set[Var]): Option[List[Sub]] = {
      var eqs = equations
      var unifier: List[Sub] = Nil
      while (eqs != Nil) {
        eqs.head match {
          case (App(f1,a1),App(f2,a2)) => eqs = (f1,f2)::(a1,a2)::eqs.tail
          case (Abs(v1,e1),Abs(v2,e2)) => eqs = (v1,v2)::(e1,e2)::eqs.tail
          case (v:Var,e:E) if unifiableVariables contains v => {
              unifier = (v -> e)::unifier 
              eqs = eqs.tail
          }
          case (e:E,v:Var) if unifiableVariables contains v => {
              unifier = (v -> e)::unifier 
              eqs = eqs.tail
          }
          case (v1:Var,v2:Var) if (v1 == v2) => eqs = eqs.tail    
          case _ => return None
        }
      }
      
      val clash: Boolean = unifier.exists(s1 => {
                            unifier.exists(s2 => {
                                ((s1._1 == s2._1) && 
                                 !(s1._2 == s2._2))    
                            })
                          })
                         
      if (clash) None else Some(unifier)
    }
  }
  

}
