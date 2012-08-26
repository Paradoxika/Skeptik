package at.logic.skeptik.judgment
package immutable

import at.logic.skeptik.expression.E
  

class SetSequent(val ant: Set[E], val suc: Set[E]) extends Sequent with SequentLike[SetSequent] { 
  def +(f:E) = new SetSequent(ant, suc + f)
  def +:(f:E) = new SetSequent(ant + f, suc)
  def -(f:E) =  new SetSequent(ant, suc - f)
  def -:(f:E) = new SetSequent(ant - f, suc)

  def union(that: Sequent) = new SetSequent(ant union that.ant.toSet, suc union that.suc.toSet)
  def diff(that: Sequent) = new SetSequent(ant diff that.ant.toSet, suc diff that.suc.toSet)
  def intersect(that:Sequent) = new SetSequent(ant intersect that.ant.toSet, suc intersect that.suc.toSet)
}

object SetSequent {
  def apply() = new SetSequent(Set(),Set())
}

