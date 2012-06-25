package skeptik.algorithm.unifier

import collection.mutable.{HashMap => MMap}
import skeptik.expression.{E,Var,App,Abs}
import skeptik.expression.substitution.immutable.Substitution
import skeptik.expression.substitution.mutable.{Substitution => MSub}


object MartelliMontanari {
 
  def apply(equations: Iterable[(E,E)])(implicit variables: Set[Var]): Option[Substitution] = {
    var eqs = equations.toSeq
    val mgu = new MSub
    while (!eqs.isEmpty) {
      eqs.head match {
        case (App(f1,a1),App(f2,a2)) => eqs = Seq((f1,f2),(a1,a2)) ++ eqs.tail
        case (Abs(v1,e1),Abs(v2,e2)) => eqs = Seq((v1,v2),(e1,e2)) ++ eqs.tail
        case (v1:Var,v2:Var) if (v1 == v2) => eqs = eqs.tail 
        case (e:E,v:Var) if variables contains v => eqs = Seq((v,e)) ++ eqs.tail
        case (v:Var,e:E) if variables contains v => {
          mgu += (v -> e) 
          val sub = Substitution(v -> e)
          eqs = for (eq <- eqs.tail) yield (sub(eq._1),sub(eq._2)) 
        }         
        case _ => return None
      }
    }
    return Some(mgu.toImmutable)
    
//    val clash: Boolean = mgu.exists(s1 => {
//                          mgu.exists(s2 => {
//                              ((s1._1 == s2._1) && 
//                               !(s1._2 == s2._2))    
//                          })
//                        })
//                       
//    if (clash) None else Some(mgu.toImmutable)
  }
}
 
