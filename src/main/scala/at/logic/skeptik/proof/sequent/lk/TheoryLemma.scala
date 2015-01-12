package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

/**
 * TheoryLemma is a class for a theory lemma for which a proof is missing.
 */
class TheoryLemma(conclusion: Sequent) extends TheoryAxiom(conclusion)

object TheoryLemma {
  def apply(conclusion: Sequent) = new TheoryLemma(conclusion)
  
  def unapply(p: SequentProofNode) = p match {
    case p: TheoryLemma => Some(p.conclusion)
    case _ => None
  }
}