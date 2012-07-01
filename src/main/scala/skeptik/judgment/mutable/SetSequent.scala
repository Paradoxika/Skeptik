package skeptik.judgment
package mutable

import collection.mutable.{Set => MSet}
import skeptik.expression.E
  

class SetSequent(val ant:MSet[E], val suc:MSet[E]) extends ASequent {
  def +=(f:E) = { suc += f ; this }
  def =+:(f:E) = { ant += f ; this }
  def -=(f:E) =  { suc -= f ; this }
  def =-:(f:E) = { ant -= f ; this }
  
  def +=(e: Either[E,E]): SetSequent = e match {
    case Left(f) => =+:(f)
    case Right(f) => +=(f)
  }
}



