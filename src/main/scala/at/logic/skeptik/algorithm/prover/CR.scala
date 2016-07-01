package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.algorithm.unifier.{MartelliMontanari => unify}
import at.logic.skeptik.expression.Var

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
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
    val ancestor = mutable.Map.empty[Clause, Set[Clause]] // For each clause what initial (input) clauses produced it
    val unifiableUnits = mutable.Map.empty[Literal, mutable.Set[Clause]] // Shows unifiable unit clauses for each literal
    val clauses = cnf.clauses.to[ArrayBuffer] // Just all clauses (for current moment)
    clauses.foreach(clause => ancestor(clause) = Set(clause)) // Ancesot of initial clauses is exactly this clause
    val literals = clauses.flatMap(_.literals)
    literals.foreach(unifiableUnits(_) = mutable.Set.empty)
    var level = 0
    levelClauses(0) = cnf.clauses // Initial clauses have level 0

    for (literal <- literals) {
      for (other <- clauses) if (other.isUnit) {
        unify((literal.unit, other.literal.unit) :: Nil) match {
          case Some(_) => unifiableUnits(literal) += other
          case None =>
        }
      }
    }

    Breaks.breakable {
      while (true) {
        val result = ArrayBuffer.empty[Clause]
        for (lastLevelClause <- levelClauses(level)) {
          // For each literal in clause we fetch what unit clauses exists which can be resolved with this literal
          // e.g. unifyCandidates for Clause(!P(X), Q(a)) can be Seq(Seq(P(a), P(b), P(f(a))), Seq(!Q(X), !Q(a)))
          val unifyCandidates = lastLevelClause.literals.map(unifiableUnits(_).toSeq)
          if (unifyCandidates.length > 1) { // If this clause is not a unit clause
            for (conclusionId <- unifyCandidates.indices) { // Id of literal which will be a conclusion
              val conclusion = lastLevelClause.literals(conclusionId)
              // All unifiers excluding that one for conclusion
              val unifiers = unifyCandidates.take(conclusionId) ++ unifyCandidates.drop(conclusionId + 1)
              // All literals excluding conclusion
              val literals = lastLevelClause.literals.take(conclusionId) ++ lastLevelClause.literals.drop(conclusionId + 1)
              for (unifier <- combinations(unifiers)) { // We should try all combinations of unifiers
                val unifierUnits = unifier.map(_.literal.unit)
                val literalUnits = literals.map(_.unit)
                unify(literalUnits.zip(unifierUnits)) match { // All unifiers should be unified with literals using one common mgu
                  case Some(mgu) =>
                    val newLiteral = (mgu(conclusion.unit), conclusion.negated)
                    val newClause = newLiteral.toClause
                    if (!clauses.contains(newClause)) {
                      result += newClause
                      ancestor(newClause) = (Set.empty[Clause] /: unifier)(_ union ancestor(_))
                    }
                  case None =>
                }
              }
            }
          }
        }
        if (result.isEmpty) {
          Breaks.break()
        }
        val usedAncestors = result.map(ancestor(_)).reduce(_ union _)
        if (usedAncestors.size != levelClauses(0).size) { // If at least one ancestor wasn't used
          val notUsedAncestors = mutable.Set((levelClauses(0).toSet diff usedAncestors).toSeq: _*) // FIXME: really, no better way?
          // We need a clause which have not used ancestor
          for (clause <- levelClauses(level)) if ((ancestor(clause) intersect notUsedAncestors).nonEmpty) {
            // TODO: Somehow detect which literals should be decided to produce a conclusion from this clause
          }
        }
        level += 1
        clauses ++= result
        levelClauses(level) = result
        for (literal <- literals) {
          for (other <- result) if (other.isUnit && other.literal.negated != literal.negated) { // FIXME: copy-pasted
            unify((literal.unit, other.literal.unit) :: Nil) match {
              case Some(_) => unifiableUnits(literal) += other
              case None =>
            }
          }
        }


        if (clauses exists { clause => clause.isUnit && unifiableUnits(clause.literal).nonEmpty }) return false
      }
    }
    true
  }
}
