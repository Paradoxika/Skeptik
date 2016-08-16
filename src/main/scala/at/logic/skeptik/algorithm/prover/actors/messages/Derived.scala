package at.logic.skeptik.algorithm.prover.actors.messages

import at.logic.skeptik.algorithm.prover.Clause
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.proof.sequent.conflictresolution

/**
  * @author Daniyar Itegulov
  */
case class Derived(clause: Clause,
                   reverseImpGraph: Map[Literal, Set[(Clause, Seq[(Literal, Substitution)])]],
                   conflict: conflictresolution.Conflict)
