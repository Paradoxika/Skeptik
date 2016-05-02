package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

/**
 * TheoryAxiom is the abstract superclass for all theory axioms
 */
abstract class TheoryAxiom(override val mainFormulas: Sequent) 
  extends SequentProofNode
  with Nullary with NoImplicitContraction
