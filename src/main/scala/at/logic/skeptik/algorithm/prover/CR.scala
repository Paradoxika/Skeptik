package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.algorithm.unifier.{MartelliMontanari => unify}
import at.logic.skeptik.expression.{Abs, App, E, Var, i}
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.expression.substitution.mutable.{Substitution => MSubstitution}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.language.postfixOps
import scala.util.Random

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

    val depthLiterals = mutable.Map.empty[Int, mutable.Set[Literal]] // Shows literals that were propagated at this depth
    depthLiterals(0) = mutable.Set.empty
    val ancestor = mutable.Map.empty[Literal, mutable.Set[Clause]] // For each literal what initial clauses produced it
    val implicationGraph = mutable.Map.empty[Clause, ArrayBuffer[Literal]] // For each clause (or literal) what literals was produced from it
    val reverseImplicationGraph = mutable.Map.empty[Literal, mutable.Set[(Clause, Seq[Literal], Substitution)]] // For each literal what clause, literals and mgu were used to produce it
    val unifiableUnits = mutable.Map.empty[Literal, mutable.Set[Literal]] // Shows unifiable literals for each literal
    val literals = mutable.Set(cnf.clauses.flatMap(_.literals): _*) // All literals contained in propagated literals and initial clauses
    val propagatedLiterals = mutable.Set.empty[Literal]
    var depth = 0 // Current depth
    val decision = ArrayBuffer.empty[Literal] // Literals, which were decided
    val conflictClauses = mutable.Set.empty[Clause]

    def allClauses: Seq[Clause] = cnf.clauses ++ conflictClauses

    // Initial unit-clauses are considered as propagated
    {
      val unitClauses = allClauses.filter(_.isUnit).map(_.literal)
      propagatedLiterals ++= unitClauses
      unitClauses.foreach(literal => ancestor.getOrElseUpdate(literal, mutable.Set.empty) += literal.toClause)
    }

    /*
     * Filling in the unifiableUnits structure: if there is some unit clauses from initial clauses, then we
     * can use them to propagate something at step 1.
     */
    literals.foreach(unifiableUnits(_) = mutable.Set.empty)
    for (literal <- literals) {
      for (other <- allClauses) if (other.isUnit && other.literal.negated != literal.negated) {
        unifyWithRename(Seq(literal.unit), Seq(other.literal.unit)) match {
          case Some(_) => unifiableUnits(literal) += other.literal
          case None =>
        }
      }
    }

    /**
      * Try to resolve given non-unit clause with some propagated literals.
      *
      * @param clause initial non-unit clause
      * @return Set of literals, which were propagated from given clause
      */
    def resolve(clause: Clause): Set[Literal] = {
      val result = mutable.Set.empty[Literal]
      // For each literal in clause we fetch what unit clauses exists which can be resolved with this literal
      // e.g. unifyCandidates for Clause(!P(X), Q(a)) can be Seq(Seq(P(a), P(b), P(f(a))), Seq(!Q(X), !Q(a)))
      val unifyCandidates = clause.literals.map(unifiableUnits.getOrElseUpdate(_, mutable.Set.empty).toSeq)
      for (conclusionId <- unifyCandidates.indices) {
        // Id of literal which will be a conclusion
        val conclusion = clause.literals(conclusionId)
        // All unifiers excluding that one for conclusion
        val unifiers = unifyCandidates.take(conclusionId) ++ unifyCandidates.drop(conclusionId + 1)
        // All literals excluding conclusion
        val literals = clause.literals.take(conclusionId) ++ clause.literals.drop(conclusionId + 1)
        for (unifier <- combinations(unifiers)) { // We should try all combinations of unifiers
          val unifierUnits = unifier.map(_.unit)
          val literalUnits = literals.map(_.unit)
          unifyWithRename(literalUnits, unifierUnits) match {
            // All unifiers should be unified with literals using one common mgu
            case Some((leftMgu, _)) =>
              val newLiteral = Literal(leftMgu(conclusion.unit), conclusion.negated)
              unifier.foreach(implicationGraph.getOrElseUpdate(_, ArrayBuffer.empty) += newLiteral)
              val newEntry = (clause, unifier, leftMgu)
              if (!unifier.exists(isAncestor(_, newLiteral))) {
                reverseImplicationGraph.getOrElseUpdate(newLiteral, mutable.Set.empty) += newEntry
                ancestor.getOrElseUpdate(newLiteral, mutable.Set.empty) ++=
                  (Set.empty[Clause] /: unifier) (_ union ancestor(_)) + clause
                if (decision.contains(newLiteral)) {
                  decision -= newLiteral
                  result += newLiteral
                }
                if (!result.contains(newLiteral) && !propagatedLiterals.contains(newLiteral)) {
                  result += newLiteral
                }
              }
            case None =>
          }
        }
      }
      result.toSet
    }

    /**
      * Check if `initial` is an ancestor of `initial` in implication graph.
      * @param current to check as a descendant
      * @param ancestor to check as an ancestor
      * @return true, if initial is ancestor of current
      *         false, otherwise
      */
    def isAncestor(current: Literal, ancestor: Literal): Boolean = {
      if (current == ancestor) return true
      if (allClauses contains current.toClause) {
        false
      } else if (decision contains current) {
        false
      } else {
        reverseImplicationGraph(current).exists {
          case (clause, unifiers, sub) => unifiers.exists(isAncestor(_, ancestor))
        }
      }
    }

    /**
      * Update system with new propagated literals from `result`.
      *
      * @param result containing new literals
      */
    def updateSystem(result: Traversable[Literal]) = {
      literals ++= result
      propagatedLiterals ++= result
      result.foreach(unifiableUnits(_) = mutable.Set.empty)
      for (literal <- literals) {
        for (other <- result) if (other.negated != literal.negated) {
          unifyWithRename(Seq(literal.unit), Seq(other.unit)) match {
            case Some(_) => unifiableUnits(literal) += other
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
    def renameVars(left: Seq[E], right: Seq[E]): (Substitution, Seq[E]) = {
      val alreadyUsed = mutable.Set.empty[Var]
      val leftSubstitution = MSubstitution.empty
      val renamedLeft = for (oneLeft <- left) yield { // Each E in left should contain unique variables
        val leftE = leftSubstitution(oneLeft)
        val sharedVars = unifiableVars(leftE) intersect unifiableVars(right: _*) // Variables contained in leftOnce and right

        if (sharedVars.nonEmpty) {
          // Unification variables which can be reused for new variables
          val notUsedVars = variables diff (sharedVars union unifiableVars(left: _*) union unifiableVars(right: _*) union alreadyUsed)

          val kvs = for (v <- sharedVars) yield {
            val replacement = notUsedVars.headOption getOrElse { // Use some variable from unification variables
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

          leftSubstitution ++= kvs

          leftSubstitution(leftE)
        } else {
          leftE
        }
      }
      (leftSubstitution.toImmutable, renamedLeft)
    }

    /**
      * Resets system to initial state and add `newClauses` as
      * conflict driven clauses.
      *
      * @param newClauses clauses to be added as conflict
      */
    def reset(newClauses: Traversable[Clause]): Unit = {
      conflictClauses ++= newClauses
      depth = 0
      depthLiterals.clear()
      depthLiterals(0) = mutable.Set.empty
      ancestor.clear()
      unifiableUnits.clear()
      literals.clear()
      literals ++= allClauses.flatMap(_.literals)
      propagatedLiterals.clear()
      decision.clear()
      reverseImplicationGraph.clear()

      literals.foreach(unifiableUnits(_) = mutable.Set.empty)
      for (literal <- literals) {
        for (other <- allClauses) if (other.isUnit && other.literal.negated != literal.negated) {
          unifyWithRename(Seq(literal.unit), Seq(other.literal.unit)) match {
            case Some(_) => unifiableUnits(literal) += other.literal
            case None =>
          }
        }
      }

      {
        val unitClauses = allClauses.filter(_.isUnit).map(_.literal)
        propagatedLiterals ++= unitClauses
        unitClauses.foreach(literal => ancestor.getOrElseUpdate(literal, mutable.Set.empty) += literal.toClause)
      }
    }

    /**
      * Pairwise unification (zipped) with renaming of mutual variables.
      *
      * @param left expressions to be unified.
      * @param right expression to be unified
      * @return Some(sub, renameSub) if there is a substitution `sub` which unifies left and right and `renameSub` which modifies left before it.
      *         None if there is no substitution.
      */
    def unifyWithRename(left: Seq[E], right: Seq[E]): Option[(Substitution, Substitution)] = {
      val (renameSubstitution, renamedLeft) = renameVars(left, right)
      val unificationProblem = renamedLeft.zip(right)
      val unificationSubstitution = unify(unificationProblem)
      unificationSubstitution.map(s => {
        val unificationRenamedSubstitution = for ((key, value) <- renameSubstitution) yield (key, s(value))
        val left = s.filterNot { case (k, v) => renameSubstitution.contains(k) }
        (new Substitution(unificationRenamedSubstitution ++ left), s)
      })
    }

    while (true) {
      val result = ArrayBuffer.empty[Literal] // New literals, which are propagated on this step
      for (clause <- allClauses if !clause.isUnit) {
        result ++= resolve(clause) // Try to resolve all clause with some other clauses
      }

      // If there is a literal in clause, which is contained either in `clauses` or `result`
      def satisfied = cnf.clauses.filter(_.literals.exists(lit => (propagatedLiterals contains lit) || (result contains lit)))

      def usedAncestors = result.map(ancestor(_)).fold(mutable.Set.empty)(_ union _) ++ satisfied
      def notUsedAncestors = Random.shuffle((cnf.clauses.toSet diff usedAncestors).toSeq)
      while (notUsedAncestors.nonEmpty) {
        // If at least one ancestor wasn't used
        val clause = notUsedAncestors.head
        // We are trying to unify `clause`, so BFS-resolution proceed with this clause.
        // So we retrieve all possible candidates for unifying of each literal and also add this
        // negated literal (we will make appropriate decision to justify this) so we can always choose
        // at least one candidate for resolution.
        val decisionLiteral = Random.shuffle(clause.literals).head
        decision += decisionLiteral
        ancestor(decisionLiteral) = mutable.Set.empty
        depthLiterals(depth) += decisionLiteral
        updateSystem(Seq(decisionLiteral))

        for (ancestor <- notUsedAncestors) {
          result ++= resolve(ancestor)
        }
      }
      println(s"Decided $decision and resolved $result")
      updateSystem(result)
      depth += 1
      depthLiterals(depth) = mutable.Set(result: _*)

      val conflictLearnedClauses = ArrayBuffer.empty[Clause]
      propagatedLiterals.filter(unifiableUnits(_).nonEmpty).foreach { conflictLiteral =>
        // For each literal, which can be unified with some other literal
        val otherLiteral = unifiableUnits(conflictLiteral).head
        println(s"There is a conflict from $conflictLiteral and $otherLiteral")

        /**
          * Finds conflict clause, used consisting of negation of all decisions-ancestors of `current`.
          *
          * @param current literal
          * @param substitution last instantiation of this literal
          * @return clause, representing disjunction of negated decision literals, used in propagation of current literal
          */
        def findConflictClause(current: Literal, substitution: Substitution = Substitution.empty): Clause = {
          if (allClauses contains current.toClause) {
            Clause.empty
          } else if (decision contains current) {
            !substitution(current)
          } else if (reverseImplicationGraph contains current) {
            val conflictClauses = for ((_, unifier, mgu) <- reverseImplicationGraph(current))
              yield unifier.map(findConflictClause(_, mgu)).fold(Clause.empty)(_ union _)
            conflictClauses.toSeq.sortBy(_.width).head
          } else {
            throw new IllegalStateException("Literal was propagated, but there is no history in implication graph")
          }
        }

        val (leftMgu, rightMgu) = unifyWithRename(Seq(conflictLiteral.unit), Seq(otherLiteral.unit)).get
        val conflictClauseLeft = findConflictClause(conflictLiteral, leftMgu)
        val conflictClauseRight = findConflictClause(otherLiteral, rightMgu)

        println(s"Conflict clause from $conflictLiteral is $conflictClauseLeft")
        println(s"Conflict clause from $otherLiteral is $conflictClauseRight")
        val newClause = conflictClauseLeft union conflictClauseRight
        println(s"Derived $newClause")
        if (newClause == Clause.empty) return false
        conflictLearnedClauses += newClause
      }

      if (conflictLearnedClauses.nonEmpty) {
        reset(conflictLearnedClauses)
      } else if (result.isEmpty) {
        return true
      }
    }
    true
  }
}
