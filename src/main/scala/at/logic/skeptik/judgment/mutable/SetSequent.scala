package at.logic.skeptik.judgment
package mutable

import collection.mutable.{Set => MSet}
import at.logic.skeptik.expression.E
  
/** A class for mutable sequents whose cedents are mutable sets.
 *
 *  @example {{{
 *  // Make a SetSequent via the companion object factory
 *  val s = SetSequent()()
 *  
 *  // Add formula f to the succedent of sequent s
 *  val s += f
 *  
 *  // Add formula f to the antecedent of sequent s
 *  val f =+: s
 *  }}}
 *
 *  @author  Bruno Woltzenlogel Paleo
 *  @version 0.2
 *  @since   0.2
 */
class SetSequent(val ant:MSet[E], val suc:MSet[E]) extends Sequent with SequentLike[SetSequent] {
  def +=(f:E) = { suc += f ; this }
  def =+:(f:E) = { ant += f ; this }
  def -=(f:E) =  { suc -= f ; this }
  def =-:(f:E) = { ant -= f ; this }
  
  def +(f:E) = new SetSequent(ant, suc + f)
  def +:(f:E) = new SetSequent(ant + f, suc)
  def -(f:E) =  new SetSequent(ant, suc - f)
  def -:(f:E) = new SetSequent(ant - f, suc)
  
  
  def union(that: Sequent) = new SetSequent(ant union that.ant.toSet, suc union that.suc.toSet)
  def diff(that: Sequent) = new SetSequent(ant diff that.ant.toSet, suc diff that.suc.toSet)
  def intersect(that:Sequent) = new SetSequent(ant intersect that.ant.toSet, suc intersect that.suc.toSet)
}

object SetSequent {
  def apply()() = new SetSequent(MSet(), MSet())
}

