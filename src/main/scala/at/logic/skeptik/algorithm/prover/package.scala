package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.expression.E
import at.logic.skeptik.judgment.immutable.SetSequent

import scala.language.implicitConversions

/**
  * @author Daniyar Itegulov
  */
package object prover {
  type Clause = SetSequent
  type CNF = structure.immutable.CNF

  object Clause {
    def apply(a: E*)(b: E*) = new SetSequent(a.toSet, b.toSet)
    def empty = SetSequent()
  }

  implicit def varToLit(variable: E): Literal = Literal(variable, negated = false)

  implicit def literalToClause(literal: Literal): Clause = literal.toClause

  implicit class ClauseOperations(clause: Clause) {
    lazy val literals: Seq[Literal] =
      (clause.ant.map(Literal(_, negated = true)) ++ clause.suc.map(Literal(_, negated = false))).toSeq

    def apply(pos: Int): Literal = literals(pos)

    def first: Literal = apply(0)

    def last: Literal = apply(literals.length - 1)

    def isUnit: Boolean = clause.width == 1
  }

  implicit class UnitSequent(sequent: SetSequent) {
    def literal: Literal =
      if (sequent.ant.size == 1 && sequent.suc.isEmpty) Literal(sequent.ant.head, negated = true)
      else if (sequent.ant.isEmpty && sequent.suc.size == 1) Literal(sequent.suc.head, negated = false)
      else throw new IllegalStateException("Given SetSequent is not a unit")
  }

  implicit class LiteralsAreSequent(literals: Iterable[Literal]) {
    def toSequent: SetSequent = {
      val ant = literals.flatMap(l => if (l.negated) Some(l.unit) else None)
      val suc = literals.flatMap(l => if (l.negated) None else Some(l.unit))
      new SetSequent(ant.toSet, suc.toSet)
    }
  }
}
