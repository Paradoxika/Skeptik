package at.logic.skeptik.algorithm.prover.actors.messages

import at.logic.skeptik.algorithm.prover.Clause
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal

/**
  * @author Daniyar Itegulov
  */
case class PropagationActorUpdate(newClauses: Seq[Clause], newUnifiableUnits: Map[Literal, Set[Literal]])
