package at.logic.skeptik.proof.sequent.conflictresolution

import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.SequentProofNode

/**
  * @author Daniyar Itegulov
  */
case class Decision(literal: Literal) extends SequentProofNode {
  override def auxFormulasMap: Map[SequentProofNode, SeqSequent] = Map.empty

  override def mainFormulas: SeqSequent = SeqSequent()()

  override def conclusionContext: SeqSequent = literal.toClause

  override def premises: Seq[SequentProofNode] = Seq.empty
}
