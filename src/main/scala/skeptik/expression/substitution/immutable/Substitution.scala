package skeptik.expression
package substitution
package immutable

import collection.immutable.MapLike
import collection.mutable.{Builder, MapBuilder}
import collection.generic.CanBuildFrom

final class Substitution (override protected val m: Map[Var, E]) 
extends AbstractSubstitution with Map[Var, E] with MapLike[Var, E, Substitution] {  
  def get(key: Var) = m.get(key)
  def iterator: Iterator[(Var, E)] = m.iterator
  def + [B >: E](kv: (Var, B)) = {
    if (kv._2.isInstanceOf[E]) new Substitution(m + kv.asInstanceOf[(Var,E)])
    else m + kv
//
//  // Due to type erasure, this always matches the first case, and creates a new Substitution even when the value is not of type E!
//  kv match {
//    case kv: (Var, E) => new Substitution(m + kv)
//    case _ => m + kv
//  }
//
//  // This causes ClassCastException when the method "map" is used 
//  m + kv
  }
  def - (key: Var)  = new Substitution(m - key) 
  override def empty = new Substitution(Map[Var,E]())  
  override def toString = "Substitution(" + m + ")"
}
object Substitution {
  def empty = new Substitution(Map[Var,E]())  
  def apply(kvs: (Var, E)*): Substitution = new Substitution(Map[Var,E](kvs:_*)) 
  
  def newBuilder: Builder[(Var, E), Substitution] = new MapBuilder[Var, E, Substitution](empty)
  
  implicit def canBuildFrom: CanBuildFrom[Substitution, (Var, E), Substitution] = 
      new CanBuildFrom[Substitution, (Var, E), Substitution] {
        def apply(from: Substitution) = newBuilder
        def apply() = newBuilder
      }
}