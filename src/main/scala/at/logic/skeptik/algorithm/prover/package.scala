package at.logic.skeptik.algorithm

import at.logic.skeptik.expression.E
import at.logic.skeptik.judgment.immutable.SetSequent

import scala.language.implicitConversions

/**
  * @author Daniyar Itegulov
  */
package object prover {
  type Clause = SetSequent
  type Literal = (E, Boolean) // Variable and isNegated
  type CNF = structure.immutable.CNF

  object Clause {
    def apply(a: E*)(b: E*) = new SetSequent(a.toSet, b.toSet)
    def empty = SetSequent()
  }

  implicit def varToLit(variable: E): Literal = (variable, false)

  implicit class ClauseOperations(clause: Clause) {
    lazy val literals: Seq[Literal] =
      (clause.ant.map((_, true)) ++ clause.suc.map((_, false))).toSeq

    def apply(pos: Int): Literal = literals(pos)

    def first: Literal = apply(0)

    def last: Literal = apply(literals.length - 1)

    def isUnit: Boolean = clause.width == 1
  }

  implicit class LiteralOperations(literal: Literal) {
    val unit: E = literal._1
    val negated: Boolean = literal._2

    def unary_! = (literal._1, !literal._2)

    def toClause: Clause = if (negated) new SetSequent(Set(unit), Set.empty) else new SetSequent(Set.empty, Set(unit))
  }

  implicit class UnitSequent(sequent: SetSequent) {
    def literal: Literal =
      if (sequent.ant.size == 1 && sequent.suc.isEmpty) (sequent.ant.head, true)
      else if (sequent.ant.isEmpty && sequent.suc.size == 1) (sequent.suc.head, false)
      else throw new IllegalStateException("Given SetSequent is not a unit")
  }

  implicit class LiteralsAreSequent(literals: Seq[Literal]) {
    def toSequent: SetSequent = {
      val ant = literals.flatMap(l => if (l.negated) Some(l.unit) else None)
      val suc = literals.flatMap(l => if (l.negated) None else Some(l.unit))
      new SetSequent(ant.toSet, suc.toSet)
    }
  }
}
