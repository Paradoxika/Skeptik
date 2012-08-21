package at.logic.skeptik.judgment
package immutable

import at.logic.skeptik.expression.E
  

class SetSequent(val ant: Set[E], val suc: Set[E]) extends ASequent { 
  def +(f:E) = new SetSequent(ant, suc + f)
  def +:(f:E) = new SetSequent(ant + f, suc)
  def -(f:E) =  new SetSequent(ant, suc - f)
  def -:(f:E) = new SetSequent(ant - f, suc)


  def ++(other:SetSequent) = new SetSequent(ant ++ other.ant, suc ++ other.suc)
  def --(other:SetSequent) = new SetSequent(ant -- other.ant, suc -- other.suc)
  def intersect(other:SetSequent) = new SetSequent(ant intersect other.ant, suc intersect other.suc)
}

object SetSequent {
  def apply() = new SetSequent(Set(),Set())
  def apply(s: Sequent) = new SetSequent(s.ant.toSet, s.suc.toSet)
}

