package at.logic.skeptik.judgment
package mutable

import collection.mutable.{Set => MSet}
import at.logic.skeptik.expression.E
  

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

object SetSequent {
  def apply() = new SetSequent(MSet(), MSet())
}

