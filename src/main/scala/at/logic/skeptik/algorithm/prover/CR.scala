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
  private def combinations[A](xss: Seq[Seq[A]]): Seq[Seq[A]] = xss match {
    case Nil => List(Nil)
    case xs :: rss => for (x <- xs; cs <- combinations(rss)) yield x +: cs
  }

  def isSatisfiable(cnf: CNF)(implicit variables: mutable.Set[Var]): Boolean = {

    val levelClauses = mutable.Map.empty[Int, Seq[Clause]] // Shows level at which clause was resolved
    val unifiableUnits = mutable.Map.empty[Literal, mutable.Set[Clause]] // Shows unifiable unit clauses for each literal
    val clauses = cnf.clauses.to[ArrayBuffer] // Just all clauses (for current moment)
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
          val unifyCandidates = lastLevelClause.literals.map(unifiableUnits(_).toSeq)
          if (unifyCandidates.length > 1) {
            for (resolventId <- unifyCandidates.indices) {
              val resolvent = lastLevelClause.literals(resolventId)
              val unifiers = unifyCandidates.take(resolventId) ++ unifyCandidates.drop(resolventId + 1)
              val literals = lastLevelClause.literals.take(resolventId) ++ lastLevelClause.literals.drop(resolventId + 1)
              for (unifier <- combinations(unifiers)) {
                val unifierUnits = unifier.map(_.literal.unit)
                val literalUnits = literals.map(_.unit)
                unify(literalUnits.zip(unifierUnits)) match {
                  case Some(mgu) =>
                    val newLiteral = (mgu(resolvent.unit), resolvent.negated)
                    val newClause = newLiteral.toClause
                    result += newClause
                  case None =>
                }
              }
            }
          }
        }
        if (result.isEmpty) {
          Breaks.break()
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

        for (clause <- clauses) if (clause.isUnit) {
          unifiableUnits(clause.literal).headOption match {
            case Some(other) => return false
            case None =>
          }
        }
      }
    }
    true
  }
}
