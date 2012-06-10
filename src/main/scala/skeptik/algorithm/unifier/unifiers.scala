package skeptik.algorithm

import scala.collection.immutable.{HashMap => IMap,HashSet => ISet}
import skeptik.judgment.Judgment
import skeptik.expression._


package object unifier {
  type Sub = Pair[Var,E]
  
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
 
