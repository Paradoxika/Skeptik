package at.logic.skeptik.judgment 
package mutable


import at.logic.skeptik.expression.E


trait SequentLike[+This <: SequentLike[This]] extends at.logic.skeptik.judgment.SequentLike[This] {
  def +=(f:E): This
  def =+:(f:E): This
  def -=(f:E): This
  def =-:(f:E): This
}