package at.logic.skeptik.algorithm.prover.actors.messages

import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.expression.substitution.immutable.Substitution

/**
  * @author Daniyar Itegulov
  */
case class Propagated(literal: Literal,
                      ancestors: Seq[Clause],
                      reverseImpGraph: Map[Literal, Set[(Clause, Seq[(Literal, Substitution)])]])
