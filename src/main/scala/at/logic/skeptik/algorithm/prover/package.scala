package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.algorithm.unifier.{MartelliMontanari => unify}
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.expression.{Abs, App, E, Var, i}
import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.judgment.immutable.SetSequent

import scala.collection.mutable
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

  implicit class ClauseOperations(clause: Sequent) {
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

  /**
    * Gets all unifiable variables (contained in `variables`) from
    * given Es.
    *
    * @param exps where unifiable variables should be found
    * @return unifiable variables contained at least once in exps
    */
  def unifiableVars(exps: E*)(implicit variables: mutable.Set[Var]): Set[Var] = exps.flatMap {
    case App(e1, e2) =>
      unifiableVars(e1) union unifiableVars(e2)
    case Abs(v, e1) =>
      unifiableVars(v) union unifiableVars(e1)
    case v: Var =>
      if (variables contains v) Set(v) else Set.empty[Var]
  }.toSet

  /**
    * Rename quantified variables in left so that they don't intersect
    * with quantified variables in right. It's necessary for unification
    * to work correctly.
    *
    * @param left where quantified variables should be renamed
    * @param usedVars already used variables
    * @return proper substitution to rename without variable collisions
    */
  def renameVars(left: E, usedVars: Set[Var])(implicit variables: mutable.Set[Var]): Substitution = {
    val sharedVars = unifiableVars(left) intersect usedVars // Variables which should be renamed

    // Unification variables which can be reused for new variables
    val notUsedVars = variables diff (sharedVars union unifiableVars(left) union usedVars)

    val kvs = for (v <- sharedVars) yield {
      val replacement = notUsedVars.headOption getOrElse { // Use some variable from unification variables
      // Or create a new one
      var newVar = Var(v + "'", i)
        while (sharedVars contains newVar) {
          newVar = Var(newVar + "'", i)
        }
        variables += newVar // It will be available for unification from now
        newVar
      }

      if (notUsedVars contains replacement) notUsedVars -= replacement
      v -> replacement
    }

    new Substitution(kvs.toMap)
  }

  /**
    * Pairwise unification (zipped) with renaming of mutual variables.
    * Left expressions are considered to have different variables:
    *
    * If left(0) contains Var("X") and left(1) contains Var("X"), then left(1)'s variable will
    * be renamed to Var("X'").
    *
    * While right expressions have common variables.
    *
    * @param left expressions to be unified, where variables are considered different
    * @param right expressions to be unified, where variables are common
    * @return Some(leftSubs, rightSub) where leftSubs contains substitution for all left expressions and rightSub
    *           is the signle substitution for all right expressions
    *         None if there is no substitution.
    */
  def unifyWithRename(left: Seq[E], right: Seq[E])
                     (implicit variables: mutable.Set[Var]): Option[(Seq[Substitution], Substitution)] = {
    var usedVars = unifiableVars(right: _*)
    val newLeftWithSub = for (oneLeft <- left) yield {
      val substitution = renameVars(oneLeft, usedVars)
      val newLeft = substitution(oneLeft)
      usedVars ++= unifiableVars(newLeft)
      (newLeft, substitution)
    }
    val newLeft = newLeftWithSub.map(_._1)
    val subs = newLeftWithSub.map(_._2)
    val unificationProblem = newLeft.zip(right)
    val unificationSubstitution = unify(unificationProblem)
    unificationSubstitution.map(s => {
      val unifiedSubs = for (renameSubstitution <- subs) yield {
        val unificationRenamedSubstitution = for ((key, value) <- renameSubstitution) yield (key, s(value))
        val left = s.filterNot { case (k, v) => renameSubstitution.contains(k) }
        new Substitution(unificationRenamedSubstitution ++ left)
      }
      (unifiedSubs, s)
    })
  }
}
