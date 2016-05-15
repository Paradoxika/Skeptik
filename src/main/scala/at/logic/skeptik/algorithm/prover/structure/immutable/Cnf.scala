package at.logic.skeptik.algorithm.prover.structure.immutable

import at.logic.skeptik.algorithm.prover.Clause
import at.logic.skeptik.algorithm.prover.structure.mutable

import scala.collection.mutable.ArrayBuffer

/**
  * @author Daniyar Itegulov
  */
case class Cnf(clauses: Seq[Clause]) {
  lazy val variables = clauses.flatMap(_.literals.map(_.unit))

  def +(that: Cnf): Cnf = new Cnf(clauses ++ that.clauses)

  def -(that: Cnf): Cnf = new Cnf(clauses.filterNot(that.clauses.toSet))

  def toMutableCnf: mutable.Cnf = new mutable.Cnf(clauses.to[ArrayBuffer])
}
