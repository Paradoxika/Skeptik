package at.logic.skeptik.proof.sequent.resolution

import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.{Binary, SequentProofNode}

/**
  * Represents Conflict rule from Conflict Resolution calculus.
  *
  * @author Daniyar Itegulov
  */
class Conflict(val leftPremise: SequentProofNode,
               val rightPremise: SequentProofNode) extends SequentProofNode with Binary {
  require(leftPremise.conclusion.width == 1, "Left premise should be a unit clause")
  require(rightPremise.conclusion.width == 1, "Right premise should be a unit clause")

  override def mainFormulas: SeqSequent = SeqSequent()()

  override def conclusionContext: SeqSequent = SeqSequent()()

  override def leftAuxFormulas: SeqSequent = leftPremise.conclusion

  override def rightAuxFormulas: SeqSequent = rightPremise.conclusion
}
