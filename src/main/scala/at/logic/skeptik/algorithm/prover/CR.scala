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
    val literals = mutable.Set(clauses.flatMap(_.literals): _*)
    literals.foreach(unifiableUnits(_) = mutable.Set.empty)
    var level = 0
    levelClauses(0) = cnf.clauses // Initial clauses have level 0
    val decision = ArrayBuffer.empty[Literal]

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
            unify(literalUnits.zip(unifierUnits)) match { // All unifiers should be unified with literals using one common mgu
              case Some(mgu) =>
                val newLiteral = (mgu(conclusion.unit), conclusion.negated)
                val newClause = newLiteral.toClause
                if (!clauses.contains(newClause)) {
                  ancestor(newClause) = (Set.empty[Clause] /: (unifier :+ clause))(_ union ancestor(_))
                  result += newClause
                }
              case None =>
            }
          }
        }
      }
      result.toSet
    }

    Breaks.breakable {
      while (true) {
        val result = ArrayBuffer.empty[Clause]
        for (lastLevelClause <- levelClauses(level)) {
          result ++= resolve(lastLevelClause)
        }
        println(s"Resolved $result")
        if (result.isEmpty) {
          Breaks.break()
        }
        var usedAncestors = result.map(ancestor(_)).reduce(_ union _)
        while (usedAncestors.size != levelClauses(0).size) { // If at least one ancestor wasn't used
          val notUsedAncestors = mutable.Set((levelClauses(0).toSet diff usedAncestors).toSeq: _*) // FIXME: really, no better way?
          // We need clauses which have unused ancestor
          val interestingClauses = levelClauses(level).filter {
            clause => (ancestor(clause) intersect notUsedAncestors).nonEmpty
          }

          interestingClauses.headOption match {
            case Some(clause) =>
              val unifyCandidates = clause.literals.map(unifiableUnits(_).toSeq)
              var bestDecision = literals.toBuffer
              // FIXME: partly copy-pasted
              if (unifyCandidates.length > 1) { // If this clause is not a unit clause
                for (conclusionId <- unifyCandidates.indices) { // Id of literal which will be a conclusion
                  // All unifiers excluding that one for conclusion
                  val unifiers = unifyCandidates.take(conclusionId) ++ unifyCandidates.drop(conclusionId + 1)
                  // All literals excluding conclusion
                  val literals = clause.literals.take(conclusionId) ++ clause.literals.drop(conclusionId + 1)

                  val needToDecide = ArrayBuffer.empty[Literal]

                  (literals /: unifiers) {
                    case (leftLiterals, unifierChoices) =>
                      val lit = leftLiterals.head
                      unifierChoices.map(unifierChoice =>
                        unify((lit.unit, unifierChoice.literal.unit) :: Nil) match {
                          case Some(mgu) =>
                            Some(leftLiterals.tail.map(l => (mgu(l.unit), l.negated)))
                          case None =>
                            None
                        }
                      ).find(_.isDefined).flatten match {
                        case Some(unifiedLiterals) =>
                          unifiedLiterals
                        case None =>
                          needToDecide += !leftLiterals.head
                          leftLiterals.tail
                      }
                  }
                  if (bestDecision.size >= needToDecide.size) {
                    bestDecision = needToDecide
                  }
                }
              }
              bestDecision.foreach(literal => {
                decision += literal
                clauses += literal.toClause
                literals += literal
                ancestor(literal.toClause) = Set.empty
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
              usedAncestors = result.map(ancestor(_)).reduce(_ union _)
            case None =>
              throw new IllegalStateException("Not all ancestors are used, but there is no 'interesting' clauses")
          }
        }
        level += 1
        clauses ++= result
        literals ++= result.flatMap(_.literals)
        levelClauses(level) = result
        for (literal <- literals) {
          for (other <- result) if (other.isUnit && other.literal.negated != literal.negated) { // FIXME: copy-pasted
            unify((literal.unit, other.literal.unit) :: Nil) match {
              case Some(_) =>
                unifiableUnits.getOrElseUpdate(literal, mutable.Set.empty) += other
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
