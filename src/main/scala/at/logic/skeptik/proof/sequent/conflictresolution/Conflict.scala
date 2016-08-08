package at.logic.skeptik.proof.sequent.conflictresolution

import at.logic.skeptik.judgment.Sequent
import at.logic.skeptik.judgment.immutable.SetSequent
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

  override def mainFormulas: Sequent = SetSequent()()

  override def conclusionContext: Sequent = SetSequent()()

  override def leftAuxFormulas: Sequent = leftPremise.conclusion

  override def rightAuxFormulas: Sequent = rightPremise.conclusion
}
