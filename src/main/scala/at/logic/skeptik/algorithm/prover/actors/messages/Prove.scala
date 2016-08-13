package at.logic.skeptik.algorithm.prover.actors.messages

import at.logic.skeptik.algorithm.prover.structure.immutable.CNF
import at.logic.skeptik.expression.Var

import scala.collection.mutable

/**
  * @author Daniyar Itegulov
  */
case class Prove(cnf: CNF, variables: mutable.Set[Var])
