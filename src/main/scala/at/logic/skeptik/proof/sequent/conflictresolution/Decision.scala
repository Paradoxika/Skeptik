package at.logic.skeptik.proof.sequent.conflictresolution

import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.SequentProofNode

/**
  * @author Daniyar Itegulov
  */
case class Decision(clause: SeqSequent) extends SequentProofNode {

  require(clause.width == 1, "Decision clause should be unit")

  override def auxFormulasMap: Map[SequentProofNode, SeqSequent] = Map.empty

  override def mainFormulas: SeqSequent = SeqSequent()()

  override def conclusionContext: SeqSequent = clause.toSeqSequent

  override def premises: Seq[SequentProofNode] = Seq.empty
}
