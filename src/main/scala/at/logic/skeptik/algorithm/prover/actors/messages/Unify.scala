package at.logic.skeptik.algorithm.prover.actors.messages

import at.logic.skeptik.algorithm.prover.structure.immutable.Literal

/**
  * @author Daniyar Itegulov
  */
case class Unify(left: Seq[Literal], right: Seq[Literal])
