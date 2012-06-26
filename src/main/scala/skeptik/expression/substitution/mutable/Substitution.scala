package skeptik.expression
package substitution
package mutable

import collection.mutable.{Map => MMap, MapLike => MMapLike}
import collection.mutable.{MapBuilder, Builder}
import collection.generic.CanBuildFrom

final class Substitution
extends AbstractSubstitution with MMap[Var, E] with MMapLike[Var, E, Substitution] {
  override protected def m = mm.toMap
  private val mm = MMap[Var, E]()
  
  def toImmutable = new immutable.Substitution(mm.toMap)
  
  def get(key: Var) = mm.get(key)
  override def update(key: Var, e: E) = mm.update(key, e)   
  override def remove(key: Var): Option[E] = mm.remove(key)
  def iterator: Iterator[(Var, E)] = mm.iterator
  def += (kv: (Var, E)): this.type = { update(kv._1, kv._2); this } 
  def -= (key: Var): this.type  = { remove(key); this }
  override def empty = new Substitution    
}
object Substitution extends {
  def empty = new Substitution
  
  def apply(kvs: (Var, E)*): Substitution = { val s = empty; for (kv <- kvs) s += kv ; s }
  
  def newBuilder: Builder[(Var, E), Substitution] = new MapBuilder[Var, E, Substitution](empty)
  
  implicit def canBuildFrom: CanBuildFrom[Substitution, (Var, E), Substitution] = 
      new CanBuildFrom[Substitution, (Var, E), Substitution] {
        def apply(from: Substitution) = newBuilder
        def apply() = newBuilder
      }
}