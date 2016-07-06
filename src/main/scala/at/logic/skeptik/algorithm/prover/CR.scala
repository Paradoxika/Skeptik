package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.algorithm.prover.structure.immutable.CNF
import at.logic.skeptik.algorithm.unifier.{MartelliMontanari => unify}
import at.logic.skeptik.expression.{Abs, App, E, Var, i}
import at.logic.skeptik.expression.substitution.immutable.Substitution

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.util.Random
import scala.util.control.Breaks

/**
  * @author Daniyar Itegulov
  */
object CR {

  /**
    * Computes all combinations of list of lists.
    * Example: combinations(Seq(Seq(1, 2), Seq(1, 3))) == Seq(Seq(1, 1), Seq(1, 3), Seq(2, 1), Seq(2, 3))
    *
    * @param xss sequence of sequences of possible elements
    * @tparam A type of elements
    * @return all possible combinations of elements
    */
  private def combinations[A](xss: Seq[Seq[A]]): Seq[Seq[A]] =
    xss.foldLeft(Seq(Seq.empty[A])) { (x, y) => for (a <- x.view; b <- y) yield a :+ b }

  def isSatisfiable(cnf: CNF)(implicit variables: mutable.Set[Var]): Boolean = {

    val levelClauses = mutable.Map.empty[Int, Seq[Clause]] // Shows level at which clause was resolved
    val ancestor = mutable.Map.empty[Clause, mutable.Set[Clause]] // For each clause what initial (input) clauses produced it
    val unifiableUnits = mutable.Map.empty[Literal, mutable.Set[Clause]] // Shows unifiable unit clauses for each literal
    val clauses = mutable.Set(cnf.clauses: _*) // Just all clauses (for current moment)
    clauses.foreach(clause => ancestor(clause) = mutable.Set(clause)) // Ancestor of initial clauses is exactly this clause
    val literals = clauses.flatMap(_.literals)
    literals.foreach(unifiableUnits(_) = mutable.Set.empty)
    var level = 0
    levelClauses(0) = cnf.clauses // Initial clauses have level 0
    val decision = ArrayBuffer.empty[Clause]
    val decisionInstantiations = mutable.Map.empty[Clause, mutable.Set[Substitution]]

    for (literal <- literals) {
      for (other <- clauses) if (other.isUnit && other.literal.negated != literal.negated) {
        unify((literal.unit, other.literal.unit) :: Nil) match {
          case Some(_) => unifiableUnits(literal) += other
          case None =>
        }
      }
    }

    def resolve(clause: Clause): Set[Clause] = {
      val result = mutable.Set.empty[Clause]
      // For each literal in clause we fetch what unit clauses exists which can be resolved with this literal
      // e.g. unifyCandidates for Clause(!P(X), Q(a)) can be Seq(Seq(P(a), P(b), P(f(a))), Seq(!Q(X), !Q(a)))
      val unifyCandidates = clause.literals.map(unifiableUnits(_).toSeq)
      if (unifyCandidates.length > 1) { // If this clause is not a unit clause
        for (conclusionId <- unifyCandidates.indices) { // Id of literal which will be a conclusion
          val conclusion = clause.literals(conclusionId)
          // All unifiers excluding that one for conclusion
          val unifiers = unifyCandidates.take(conclusionId) ++ unifyCandidates.drop(conclusionId + 1)
          // All literals excluding conclusion
          val literals = clause.literals.take(conclusionId) ++ clause.literals.drop(conclusionId + 1)
          for (unifier <- combinations(unifiers)) { // We should try all combinations of unifiers
            val unifierUnits = unifier.map(_.literal.unit)
            val literalUnits = literals.map(_.unit)
            val unificationProblem = renameVars(literalUnits, unifierUnits).zip(unifierUnits)
            unify(unificationProblem) match { // All unifiers should be unified with literals using one common mgu
              case Some(mgu) =>
                val newLiteral = (mgu(conclusion.unit), conclusion.negated)
                val newClause = newLiteral.toClause
                ancestor.getOrElseUpdate(newClause, mutable.Set.empty) ++=
                  (Set.empty[Clause] /: (unifier :+ clause))(_ union ancestor(_))
                (unifier :+ clause).filter(decision contains _).foreach {
                  c => decisionInstantiations.getOrElseUpdate(c, mutable.Set.empty) += mgu
                }
                if (!clauses.contains(newClause)) {
                  result += newClause
                }
              case None =>
            }
          }
        }
      }
      result.toSet
    }

    def updateClauses(result: Traversable[Clause]) = {
      clauses ++= result
      literals ++= result.flatMap(_.literals)
      for (literal <- literals) {
        for (other <- result) if (other.isUnit && other.literal.negated != literal.negated) {
          val renamedLiteral = renameVars(Seq(literal.unit), Seq(other.literal.unit)).head
          unify((renamedLiteral, other.literal.unit) :: Nil) match {
            case Some(_) =>
              unifiableUnits.getOrElseUpdate(literal, mutable.Set.empty) += other
            case None =>
          }
        }
      }
    }

    /**
      * Gets all unifiable variables (contained in `variables`) from
      * given Es.
      *
      * @param exps where unifiable variables should be found
      * @return unifiable variables contained at least once in exps
      */
    def unifiableVars(exps: E*): Set[Var] = exps.flatMap {
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
      * @param right other resolvent
      * @return `left` with renamed variables
      */
    def renameVars(left: Seq[E], right: Seq[E]): Seq[E] = {
      val alreadyUsed = mutable.Set.empty[Var]
      for (oneLeft <- left) yield { // Each E in left should contain unique variables
        val sharedVars = unifiableVars(oneLeft) intersect unifiableVars(right: _*) // Variables contained in leftOnce and right

        if (sharedVars.nonEmpty) {
          // Unification variables which can be reused for new variables
          val notUsedVars = variables diff (sharedVars union unifiableVars(left: _*) union unifiableVars(right: _*) union alreadyUsed)

          val kvs = for (v <- sharedVars) yield {
            val replacement = notUsedVars.headOption getOrElse { // Use some variable from uniciation variables
              // Or create a new one
              var newVar = new Var(v + "'", i)
              while (sharedVars contains newVar) {
                newVar = new Var(newVar + "'", i)
              }
              variables += newVar // It will be avaiable for unification from now
              newVar
            }

            alreadyUsed += replacement

            if (notUsedVars contains replacement) notUsedVars -= replacement
            v -> replacement
          }

          val sub = Substitution(kvs.toSeq: _*)
          sub(oneLeft)
        } else {
          oneLeft
        }
      }
    }

    Breaks.breakable {
      while (true) {
        val result = ArrayBuffer.empty[Clause]
        for (lastLevelClause <- levelClauses(level)) {
          result ++= resolve(lastLevelClause)
        }
        if (result.isEmpty) {
          Breaks.break()
        }
        var usedAncestors = result.map(ancestor(_)).fold(mutable.Set.empty)(_ union _) ++ levelClauses(0).filter(_.literals.exists(clauses contains _.toClause))
        while (usedAncestors.size != levelClauses(0).size) { // If at least one ancestor wasn't used
          val notUsedAncestors = mutable.Set((levelClauses(0).toSet diff usedAncestors).toSeq: _*) // FIXME: really, no better way?
          // We need clauses which have unused ancestor
          val interestingClauses = Random.shuffle(levelClauses(level).filter {
            clause => (ancestor(clause) intersect notUsedAncestors).nonEmpty
          })

          interestingClauses.headOption match {
            case Some(clause) =>
              val unifyCandidates = clause.literals.map(lit => unifiableUnits(lit).toSeq :+ (!lit).toClause)
              var bestDecision = literals.toBuffer
              for (conclusionId <- unifyCandidates.indices) { // Id of literal which will be a conclusion
                // All unifiers excluding that one for conclusion
                val unifiers = unifyCandidates.take(conclusionId) ++ unifyCandidates.drop(conclusionId + 1)
                // All literals excluding conclusion
                val literals = clause.literals.take(conclusionId) ++ clause.literals.drop(conclusionId + 1)

                val needToDecide = ArrayBuffer.empty[Literal]
                for (unifier <- combinations(unifiers).toSet[Seq[Clause]]) {
                  val unifierUnits = unifier.map(_.literal.unit)
                  val literalUnits = literals.map(_.unit)
                  val unificationProblem = renameVars(literalUnits, unifierUnits).zip(unifierUnits)
                  unify(unificationProblem) match { // All unifiers should be unified with literals using one common mgu
                    case Some(mgu) =>
                      for (u <- unifier) if (!clauses.contains(u)) {
                        needToDecide ++= u.literals
                      }
                    case None =>
                  }
                }
                if (bestDecision.size >= needToDecide.size) {
                  bestDecision = needToDecide
                }
              }
              bestDecision.foreach(literal => {
                decision += literal.toClause
                clauses += literal.toClause
                literals += literal
                ancestor(literal.toClause) = mutable.Set.empty
              })
              for (literal <- literals) {
                for (otherLiteral <- bestDecision) if (otherLiteral.negated != literal.negated) { // FIXME: copy-pasted
                  unify((literal.unit, otherLiteral.unit) :: Nil) match {
                    case Some(_) =>
                      unifiableUnits.getOrElseUpdate(literal, mutable.Set.empty) += otherLiteral.toClause
                    case None =>
                  }
                }
              }
              result ++= resolve(clause)
              updateClauses(result)
              for (lastLevelClause <- levelClauses(level)) {
                result ++= resolve(lastLevelClause)
              }
              updateClauses(result)
              usedAncestors = result.map(ancestor(_)).fold(mutable.Set.empty)(_ union _)
              if (clauses exists { clause => clause.isUnit && unifiableUnits.getOrElseUpdate(clause.literal, mutable.Set.empty).nonEmpty }) {
                val newClause = decision.flatMap(d => decisionInstantiations.getOrElse(d, mutable.Set.empty).map {
                  sub => (sub(d.literal.unit), !d.literal.negated)
                }).toSequent
                return isSatisfiable(CNF(cnf.clauses :+ newClause))
              }
            case None =>
              throw new IllegalStateException("Not all ancestors are used, but there is no 'interesting' clauses")
          }
        }
        level += 1
        updateClauses(result)
        levelClauses(level) = result


        if (clauses exists { clause => clause.isUnit && unifiableUnits(clause.literal).nonEmpty }) return false
      }
    }
    true
  }
}
