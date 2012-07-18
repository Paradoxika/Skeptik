package at.logic.skeptik.judgment
package mutable

import collection.mutable.{Set => MSet}
import at.logic.skeptik.expression.E
  
/** A class for mutable sequents.
 *
 *  @example {{{
 *  // Make a SetSequent via the companion object factory
 *  val sequent = SetSequent()
 *  }}}
 *
 *  @author  Bruno Woltzenlogel Paleo
 *  @version 0.2
 *  @since   0.2
 *  @see  [["http://www.logic.at/" "Guide"]] for more information.
 */
class SetSequent(val ant:MSet[E], val suc:MSet[E]) extends ASequent {
  /** Adds a formula to the succedent of the sequent.
   *  @param f the formula to be added.
   *  @return the sequent itself.
   *  @example `s += f`
   */
  def +=(f:E) = { suc += f ; this }
  def =+:(f:E) = { ant += f ; this }
  def -=(f:E) =  { suc -= f ; this }
  def =-:(f:E) = { ant -= f ; this }
  
  @deprecated("Use either `sequent += e` or `e =+: sequent` instead", "0.2") 
  def +=(e: Either[E,E]): SetSequent = e match {
    case Left(f) => =+:(f)
    case Right(f) => +=(f)
  }
}

object SetSequent {
  def apply() = new SetSequent(MSet(), MSet())
}

