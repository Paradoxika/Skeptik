package at.logic.skeptik.judgment
package immutable

import at.logic.skeptik.expression.E
  

class SetSequent(val ant: Set[E], val suc: Set[E]) extends ASequent { 
  def +(f:E) = new SetSequent(ant, suc + f)
  def +:(f:E) = new SetSequent(ant + f, suc)
  def -(f:E) =  new SetSequent(ant, suc - f)
  def -:(f:E) = new SetSequent(ant - f, suc)

  def intersect(that:SetSequent) = new SetSequent(ant intersect that.ant, suc intersect that.suc)
}

object SetSequent {
  def apply() = new SetSequent(Set(),Set())
}

