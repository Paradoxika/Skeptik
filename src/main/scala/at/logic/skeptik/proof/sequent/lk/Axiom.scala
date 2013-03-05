package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression.E


class Axiom(override val mainFormulas: Sequent) extends SequentProofNode
with Nullary with NoImplicitContraction {
  override def activeAncestry(f: E, premise: SequentProofNode) = throw new Exception("Active formulas in axioms have no ancestors.")
}

object Axiom {
  def apply(conclusion: Sequent) = new Axiom(conclusion)
  def unapply(p: SequentProofNode) = p match {
    case p: Axiom => Some(p.conclusion)
    case _ => None
  }
}