package at.logic.skeptik.judgment.immutable

import at.logic.skeptik.expression.Var
import at.logic.skeptik.judgment.SequentLike

/**
  * Represents a sequent with exactly one variable.
  *
  * @author Daniyar Itegulov
  */
case class UnitSequent(unit: Var, negated: Boolean) extends VarSeqSequent(
  if (negated) Seq(unit) else Seq(),
  if (negated) Seq() else Seq(unit)
) with SequentLike[SeqSequent] {
  def unary_! = new UnitSequent(unit, !negated)
}