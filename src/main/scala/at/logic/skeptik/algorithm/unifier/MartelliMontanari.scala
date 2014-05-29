package at.logic.skeptik.algorithm.unifier

import collection.mutable.{HashMap => MMap, Set => MSet}
import at.logic.skeptik.expression.{E,Var,App,Abs}
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.expression.substitution.mutable.{Substitution => MSub}

object MartelliMontanari {
  def apply(equations: Iterable[(E,E)])(implicit variables: MSet[Var]): Option[Substitution] = {
    var eqs = equations.toSeq
    val mgu = new MSub
    
    var counter = 0 
    
    while (!eqs.isEmpty) {
      //println()
      //println("Eqs: " + eqs)
      //println("Head: " + eqs.head)
      
      counter = counter + 1
//      if (counter > 100) { //10 is too small.
//        println("counter maxed out")
//        return None
//      }
      
      
      eqs.head match {
        case (App(f1,a1),App(f2,a2)) => eqs = Seq((f1,f2),(a1,a2)) ++ eqs.tail
        case (Abs(v1,e1),Abs(v2,e2)) => eqs = Seq((v1,v2),(e1,e2)) ++ eqs.tail
        case (v1:Var,v2:Var) if (v1 == v2) => eqs = eqs.tail 
        case (v:Var,e:E) if variables contains v => {
          // without occur-check
          mgu += (v -> e) 
          val sub = Substitution(v -> e)
          //println("mgu sub: " + sub)
          //println("MGU: " + mgu)
          
          eqs = for (eq <- eqs.tail) yield {
            //println("   Eq: " + eq +  " ; SubEq: " + (sub(eq._1),sub(eq._2)))
            (sub(eq._1),sub(eq._2)) 
          }
        } 
        case (e:E,v:Var) if variables contains v => eqs = Seq((v,e)) ++ eqs.tail
        case _ => return {
          None
        }
      }
    }
    return Some(mgu.toImmutable)
  }
}
 
