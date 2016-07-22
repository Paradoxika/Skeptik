package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.algorithm.unifier.{MartelliMontanari => unify}
import at.logic.skeptik.expression.{Abs, App, E, Var, i}
import at.logic.skeptik.expression.substitution.immutable.Substitution

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.language.postfixOps
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
    val implicationGraph = mutable.Map.empty[Clause, ArrayBuffer[Clause]]
    val reverseImplicationGraph = mutable.Map.empty[Clause, ArrayBuffer[(Seq[Clause], Substitution)]]
    val unifiableUnits = mutable.Map.empty[Literal, mutable.Set[Clause]] // Shows unifiable unit clauses for each literal
    val clauses = mutable.Set(cnf.clauses: _*) // Just all clauses (for current moment)
    clauses.foreach(clause => ancestor(clause) = mutable.Set(clause)) // Ancestor of initial clauses is exactly this clause
    val literals = clauses.flatMap(_.literals)
    literals.foreach(unifiableUnits(_) = mutable.Set.empty)
    var level = 0
    levelClauses(0) = cnf.clauses // Initial clauses have level 0
    val decision = ArrayBuffer.empty[Clause]
    val decisionInstantiations = mutable.Map.empty[Clause, mutable.Set[Substitution]]
    val conflictClauses = mutable.Set.empty[Clause] // Clauses learned from conflicts

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
      val unifyCandidates = clause.literals.map(unifiableUnits.getOrElseUpdate(_, mutable.Set.empty).toSeq)
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
            unifyWithRename(literalUnits, unifierUnits) match {
              // All unifiers should be unified with literals using one common mgu
              case Some(mgu) =>
                val newLiteral = (mgu(conclusion.unit), conclusion.negated)
                val newClause = newLiteral.toClause
                ancestor.getOrElseUpdate(newClause, mutable.Set.empty) ++=
                  (Set.empty[Clause] /: (unifier :+ clause))(_ union ancestor(_))
                (unifier :+ clause).filter(decision contains _).foreach {
                  c => decisionInstantiations.getOrElseUpdate(c, mutable.Set.empty) += mgu
                }
                if (!clauses.contains(newClause)) {
                  unifier.foreach(implicationGraph.getOrElseUpdate(_, ArrayBuffer.empty) += newClause)
                  reverseImplicationGraph.getOrElseUpdate(newClause, ArrayBuffer.empty) += ((unifier, mgu))
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
          unifyWithRename(Seq(literal.unit), Seq(other.literal.unit)) match {
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
              var newVar = Var(v + "'", i)
              while (sharedVars contains newVar) {
                newVar = Var(newVar + "'", i)
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

    def reset(newClause: Clause): Unit = {
      conflictClauses += newClause
      level = 0
      levelClauses.clear()
      ancestor.clear()
      unifiableUnits.clear()
      clauses.clear()
      clauses ++= cnf.clauses ++ conflictClauses
      cnf.clauses.foreach(clause => ancestor(clause) = mutable.Set(clause))
      conflictClauses.foreach(clause => ancestor(clause) = mutable.Set.empty)
      literals.clear()
      literals ++= clauses.flatMap(_.literals)
      literals.foreach(unifiableUnits(_) = mutable.Set.empty)
      levelClauses(0) = cnf.clauses ++ conflictClauses
      decision.clear()
      decisionInstantiations.clear()

      for (literal <- literals) {
        for (other <- clauses) if (other.isUnit && other.literal.negated != literal.negated) {
          unifyWithRename(Seq(literal.unit), Seq(other.literal.unit)) match {
            case Some(_) => unifiableUnits(literal) += other
            case None =>
          }
        }
      }
    }

    def unifyWithRename(left: Seq[E], right: Seq[E]): Option[Substitution] = {
      val unificationProblem = renameVars(left, right).zip(right)
      unify(unificationProblem)
    }

    def isUnifiable(left: E, right: E): Boolean = {
      val renamedLeft = renameVars(Seq(left), Seq(right)).head
      unify((renamedLeft, right) :: Nil).isDefined
    }

    var finished = false
    while (!finished) {
      Breaks.breakable {
        while (true) {
          val result = ArrayBuffer.empty[Clause] // New clauses, which will be added to `clauses` after this iteration
          for (lastLevelClause <- levelClauses(level)) {
            result ++= resolve(lastLevelClause) // Try to resolve last-level clauses with some other clauses
          }
          val satisfied = cnf.clauses.filter(_.literals.exists(lit => // If there is a literal in clause, which is
            (clauses contains lit.toClause) || (result contains lit.toClause))) // contained either in `clauses` or `result`
          var usedAncestors = result.map(ancestor(_)).fold(mutable.Set.empty)(_ union _) ++ satisfied
          while (usedAncestors.size != cnf.clauses.size) {
            // If at least one ancestor wasn't used
            val notUsedAncestors = mutable.Set((cnf.clauses.toSet diff usedAncestors).toSeq: _*)
            // We need clauses from last level which have unused ancestor
            val interestingClauses = Random.shuffle(levelClauses(level).filter {
                clause => (ancestor(clause) intersect notUsedAncestors).nonEmpty
              })

            interestingClauses.headOption match {
              case Some(clause) =>
                // We are trying to unify `clause`, so BFS-resolution proceed with this clause.
                // So we retrieve all possible candidates for unifying of each literal and also add this
                // negated literal (we will make appropriate decision to justify this) so we can always choose
                // at least one candidate for resolution.
                val unifyCandidates = clause.literals.map(lit => unifiableUnits(lit).toSeq :+ (!lit).toClause)
                var bestDecision = literals.toBuffer // Represents best (by some measure) set of literals which should
                                                     // be decided to resolve this clause.
                for (conclusionId <- unifyCandidates.indices) { // Id of literal which will be a conclusion
                  // All unifiers excluding that one for conclusion
                  val unifiers = unifyCandidates.take(conclusionId) ++ unifyCandidates.drop(conclusionId + 1)
                  // All literals excluding conclusion
                  val literals = clause.literals.take(conclusionId) ++ clause.literals.drop(conclusionId + 1)
                  for (unifier <- Random.shuffle(combinations(unifiers))) { // Try every combination of unifiers
                    val unifierUnits = unifier.map(_.literal.unit)
                    val literalUnits = literals.map(_.unit)
                    unifyWithRename(literals.map(_.unit), unifierUnits) match {
                      // All unifiers should be unified with literals using one common mgu
                      case Some(mgu) =>
                        val shouldDecide = unifier.filterNot(clauses contains).flatMap(_.literals)
                        if (bestDecision.size >= shouldDecide.size) {
                          bestDecision = shouldDecide.toBuffer
                        }
                      case None =>
                    }
                  }
                }
                bestDecision.foreach(literal => {
                  decision += literal.toClause
                  clauses += literal.toClause
                  literals += literal
                  ancestor(literal.toClause) = mutable.Set.empty
                })
                // FIXME: move this to a separate method
                for (literal <- literals) {
                  for (otherLiteral <- bestDecision) if (otherLiteral.negated != literal.negated) {
                    unifyWithRename(Seq(literal.unit), Seq(otherLiteral.unit)) match {
                      case Some(_) =>
                        unifiableUnits.getOrElseUpdate(literal, mutable.Set.empty) += otherLiteral.toClause
                      case None =>
                    }
                  }
                }
                result ++= resolve(clause) // Resolve this clauses after making necessary decisions
                updateClauses(result)
                for (lastLevelClause <- levelClauses(level)) {
                  result ++= resolve(lastLevelClause)
                }
                updateClauses(result)
                usedAncestors = result.map(ancestor(_)).fold(mutable.Set.empty)(_ union _)
                if (clauses exists { clause => clause.isUnit && unifiableUnits.getOrElseUpdate(clause.literal, mutable.Set.empty).nonEmpty }) {
                  val instances = decision.flatMap(d => decisionInstantiations.getOrElse(d, mutable.Set.empty).map {
                    sub => (sub(d.literal.unit), !d.literal.negated)
                  })
                  val mostGeneralInstances = mutable.Set.empty[Literal]
                  val satisfiedInstances = mutable.Set.empty[Literal]
                  for (inst <- instances) {
                    if (!satisfiedInstances.contains(inst)) {
                      val unifiable = instances.filter(other => inst.negated == other.negated && isUnifiable(inst.unit, other.unit))
                      satisfiedInstances ++= unifiable
                      mostGeneralInstances += unifiable.sortBy(u => u.unit.logicalSize - unifiableVars(u.unit).size).head
                    }
                  }

                  val newClause = mostGeneralInstances.toSequent

                  reset(newClause)
                  Breaks.break()
                }
              case None =>
                throw new IllegalStateException("Not all ancestors are used, but there is no 'interesting' clauses")
            }
          }
          level += 1
          updateClauses(result)
          levelClauses(level) = result


          if (clauses contains Clause.empty) {
            if (decision.isEmpty) return false

            def findConflictClause(current: Clause, substitution: Substitution = Substitution.empty): Clause = {
              if (reverseImplicationGraph contains current) {
                val conflictClauses = for ((unifier, mgu) <- reverseImplicationGraph(current))
                  yield unifier.map(findConflictClause(_, substitution ++ mgu)).fold(Clause.empty)(_ union _)
                conflictClauses.sortBy(_.width).head
              } else {
                if (decision contains current) {
                  (substitution(current.literal.unit), current.literal.negated).toClause
                } else {
                  Clause.empty
                }
              }
            }

            val newClause = findConflictClause(Clause.empty)
            reset(newClause)
            Breaks.break()
          }

          if (result.isEmpty) {
            finished = true
            Breaks.break()
          }
        }
      }
    }
    true
  }
}
