package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression.E


class UncheckedInference(override val name: String, 
                         override val premises: Seq[SequentProofNode], 
                         c: Sequent) 
extends SequentProofNode {
  def auxFormulasMap = throw new Exception("undefined")
  def mainFormulas = throw new Exception("undefined")
  def conclusionContext = throw new Exception("undefined")
  override lazy val conclusion = c
}

object UncheckedInference {
  def apply(conclusion: Sequent) = new Axiom(conclusion)
  def unapply(p: SequentProofNode) = p match {
    case p: UncheckedInference => Some(p.name, p.premises, p.conclusion)
    case _ => None
  }
}