package at.logic.skeptik.proof.sequent.conflictresolution

import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.judgment.immutable.{SeqSequent, SetSequent}
import at.logic.skeptik.proof.sequent.SequentProofNode

/**
  * @author Daniyar Itegulov
  */
case class ConflictDrivenClauseLearning(conflict: Conflict) extends SequentProofNode {

  private def findDecisions(proofNode: SequentProofNode, sub: Substitution): Sequent = {
    proofNode match {
      case Decision(clause) =>
        !sub(clause.literals.head)
      case conflict@Conflict(left, right) =>
        findDecisions(left, conflict.leftMgu) union findDecisions(right, conflict.rightMgu)
      case resolution@UnitPropagationResolution(left, right, _) =>
        // We don't need to traverse right premise, because it's either initial clause or conflict driven clause
        left.zip(resolution.leftMgus).map {
          case (node, mgu) => findDecisions(node, mgu(sub))
        }.fold(SetSequent.empty)(_ union _)
      case _ =>
        SetSequent.empty
    }
  }

  val conflictDrivenClause = findDecisions(conflict, Substitution.empty)

  override def auxFormulasMap: Map[SequentProofNode, SeqSequent] = Map.empty

  override def mainFormulas: SeqSequent = SeqSequent()()

  override def conclusionContext: SeqSequent = conflictDrivenClause.toSeqSequent

  override def premises: Seq[SequentProofNode] = Seq(conflict)
}
