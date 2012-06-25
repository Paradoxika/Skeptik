package skeptik.expression
package substitution
package immutable

import collection.immutable.{Map => IMap, MapLike => IMapLike}

class Substitution(override protected val m: IMap[Var, E]) 
extends AbstractSubstitution with IMap[Var, E] with IMapLike[Var, E, Substitution] {  
  def get(key: Var) = m.get(key)
  def iterator: Iterator[(Var, E)] = m.iterator
  def + [B >: E](kv: (Var, B)) = m + kv // TODO: (Bruno) should be "new Substitution(m + kv)" 
  def - (key: Var)  = new Substitution(m - key) 
  override def empty = new Substitution(IMap[Var,E]())    
}
object Substitution {
  def empty = new Substitution(IMap[Var,E]())  
  def apply(kvs: (Var, E)*): Substitution = new Substitution(IMap[Var,E](kvs:_*)) 
}