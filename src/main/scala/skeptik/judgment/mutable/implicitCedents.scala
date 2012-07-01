package skeptik.judgment

import collection.mutable.{Set => MSet}
import skeptik.expression.E

package object mutable {
  implicit object MSetOfEIsCedent extends Cedent[MSet[E]] {
    def add(c: MSet[E], e: E) = c += e
    def remove(c: MSet[E], e: E) = c -= e
    def contains(c: MSet[E], e: E) = c contains e
    def toList(c: MSet[E]) = c.toList
    def size(c: MSet[E]) = c.size
  } 
}


