package at.logic.skeptik.judgment.immutable

import at.logic.skeptik.expression.Var

/**
  * Represents a sequent with exactly one variable.
  *
  * @author Daniyar Itegulov
  */
case class UnitSequent(unit: Var, negated: Boolean) extends VarSeqSequent(
  if (negated) Seq(unit) else Seq(),
  if (negated) Seq() else Seq(unit)
) {
  def unary_! = new UnitSequent(unit, !negated)
}