package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.congruence.structure.EqW

class EqSymmetric(mainFormulas: Sequent) extends TheoryAxiom(mainFormulas)

object EqSymmetric {
  def apply(eq: EqW) = {
    new EqSymmetric(new Sequent(Seq(eq.equality),Seq(eq.reverseEquality)))
  }
  def apply(conclusion: Sequent) = new EqSymmetric(conclusion)

  def unapply(p: SequentProofNode) = p match {
    case p: EqSymmetric => Some(p.conclusion)
    case _ => None
  }
}