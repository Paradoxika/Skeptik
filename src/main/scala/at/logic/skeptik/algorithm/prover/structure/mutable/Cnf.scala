package at.logic.skeptik.algorithm.prover.structure.mutable

import at.logic.skeptik.algorithm.prover._

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.util.control.Breaks

/**
  * Represents propositional CNF.
  *
  * @author Daniyar Itegulov
  */
class Cnf(val clauses: ArrayBuffer[Clause]) {
  /**
    * Shows which literals are set to be true.
    */
  val assessment = mutable.Set.empty[Literal]

  /**
    * Just all variables, contained in CNF.
    */
  val variables = clauses.flatMap(_.literals.map(_.unit))

  /**
    * Represents two-watched literal scheme:
    * for each literal we know what clauses have watchers set
    * to this literal.
    */
  val sentinels: Map[Literal, mutable.Set[Clause]] = {
    val sentinels = variables.flatMap(variable =>
      Seq(
        varToLit(variable) -> mutable.Set.empty[Clause],
        !variable -> mutable.Set.empty[Clause]
      )
    ).toMap
    for (clause <- clauses) if (clause.width >= 2) {
      sentinels(clause.first) += clause
      sentinels(clause.last) += clause
    }
    sentinels
  }

  def +=(that: Clause): Cnf = {
    if (that.width >= 1) {
      sentinels(that.first) += that
      sentinels(that.last) += that
    }
    clauses += that
    this
  }

  def -=(that: Clause): Cnf = {
    if (clauses.contains(that) && that.width >= 1) {
      sentinels(that.first) -= that
      sentinels(that.last) -= that
    }
    clauses -= that
    this
  }

  private def clauseIsSatisfied(clause: Clause): Boolean = clause.literals.exists(assessment.contains)

  /**
    * Ensures that provided literal is true and returns sequence
    * of literals that should also be true.
    *
    * @param literal which should be true
    * @return sequence of literals that also should be true
    */
  def assignLiteral(literal: Literal): Seq[Literal] = {
    // FIXME: it works, but implementation is REALLY ugly
    assessment += literal
    val result = ArrayBuffer.empty[Literal]
    for (clause <- sentinels(!literal)) if (!clauseIsSatisfied(clause)) {
      var otherSentinel: Option[Literal] = None
      Breaks.breakable {
        for (otherLit <- clause.literals) if (otherLit != !literal) {
          if (sentinels(otherLit) contains clause) {
            otherSentinel = Some(otherLit)
          } else {
            sentinels(!literal) -= clause
            sentinels(otherLit) += clause
            otherSentinel = None
            Breaks.break
          }
        }
      }
      otherSentinel match {
        case Some(sentinel) => result += sentinel
        case _ =>
      }
    }
    result
  }
}
