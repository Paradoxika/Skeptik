package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.algorithm.unifier.{MartelliMontanari => unify}
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.expression.{Abs, App, E, Var, i}
import at.logic.skeptik.judgment.immutable.SeqSequent

import scala.collection.mutable
import scala.language.implicitConversions

/**
  * @author Daniyar Itegulov
  */
package object prover {
  type Clause = SeqSequent
  type CNF = structure.immutable.CNF

  object Clause {
    def apply(a: E*)(b: E*) = new SeqSequent(a, b)
    def empty = SeqSequent()()
  }

  implicit def varToLit(variable: E): Literal = Literal(variable, negated = false)

  implicit def literalToClause(literal: Literal): Clause = literal.toClause

  implicit class ClauseOperations(clause: SeqSequent) {
    lazy val literals: Seq[Literal] =
      clause.ant.map(Literal(_, negated = true)) ++ clause.suc.map(Literal(_, negated = false))

    def apply(pos: Int): Literal = literals(pos)

    def first: Literal = apply(0)

    def last: Literal = apply(literals.length - 1)

    def isUnit: Boolean = clause.width == 1
  }

  implicit class UnitSequent(sequent: SeqSequent) {
    def literal: Literal =
      if (sequent.ant.size == 1 && sequent.suc.isEmpty) Literal(sequent.ant.head, negated = true)
      else if (sequent.ant.isEmpty && sequent.suc.size == 1) Literal(sequent.suc.head, negated = false)
      else throw new IllegalStateException("Given SeqSequent is not a unit")
  }

  implicit class LiteralsAreSequent(literals: Iterable[Literal]) {
    def toSequent: SeqSequent = {
      val ant = literals.flatMap(l => if (l.negated) Some(l.unit) else None)
      val suc = literals.flatMap(l => if (l.negated) None else Some(l.unit))
      new SeqSequent(ant.toSeq, suc.toSeq)
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

  /**
    * Checks if there is such unification, which don't use unification variables from `what`.
    *
    * @param what what should be instantiated
    * @param from from what should be instantiated
    * @param variables unifiaction variables
    * @return true, if there exists some unification for what and from according to rules
    *         false, otherwise
    */
  def isInstantiation(what: E, from: E)(implicit variables: mutable.Set[Var]): Boolean = {
    val usedVars = unifiableVars(what)
    val sub = renameVars(from, usedVars)
    val newFrom = sub(from)
    val newVars = unifiableVars(what)
    variables --= newVars // newVars are fixed
    val result = unify((what, newFrom) :: Nil) match {
      case None => false
      case Some(_) => true
    }
    variables ++= newVars // Should revert variables set back to initial state
    result
  }

  /**
    * Leaves only unique literals in sequent.
    *
    * @param sequent initial sequent
    * @return initial sequent, where duplicate literals were removed
    */
  def unique(sequent: SeqSequent) = {
    def loop(set: Set[Literal], literals: Seq[Literal]): Seq[Literal] = literals match {
      case hd :: tail if set contains hd => loop(set, tail)
      case hd :: tail => hd +: loop(set + hd, tail)
      case Nil => Nil
    }

    loop(Set(), sequent.literals).toSequent
  }

  /**
    * Computes all combinations of list of lists.
    * Example: combinations(Seq(Seq(1, 2), Seq(1, 3))) == Seq(Seq(1, 1), Seq(1, 3), Seq(2, 1), Seq(2, 3))
    *
    * @param xss sequence of sequences of possible elements
    * @tparam A type of elements
    * @return all possible combinations of elements
    */
  def combinations[A](xss: Seq[Seq[A]]): Seq[Seq[A]] =
    xss.foldLeft(Seq(Seq.empty[A])) { (x, y) => for (a <- x.view; b <- y) yield a :+ b }
}
