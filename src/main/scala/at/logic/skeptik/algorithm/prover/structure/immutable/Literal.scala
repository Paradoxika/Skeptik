package at.logic.skeptik.algorithm.prover.structure.immutable

import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.expression.E
import at.logic.skeptik.judgment.immutable.SeqSequent

/**
  * Created by itegulov on 28.07.16.
  */
case class Literal(unit: E, negated: Boolean) {
  def unary_! = Literal(unit, !negated)

  def toClause: Clause = if (negated) new SeqSequent(Seq(unit), Seq.empty) else new SeqSequent(Seq.empty, Seq(unit))

  override def toString: String = if (negated) s"$unit ⊢" else s"⊢ $unit"
}
