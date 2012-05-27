package ResK.proofs.naturalDeduction

import ResK.expressions.E
import ResK.formulas.Imp
import ResK.positions.Position
import ResK.proofs.naturalDeductionWithSequentNotation.{ImpElimCArrow,RightArrow,LeftArrow}

// ToDo: Add Intuitionistic Soundness Condition

class ImpIntroC(val premise: NaturalDeductionProof, val assumption: NamedE, val position: Position)
extends NaturalDeductionProof("ImpIntro",premise::Nil) {
  require(premise.context contains assumption)
  require(position isPositiveIn premise.conclusion)
  override val context = premise.context - assumption
  override val conclusion = (((e:E) => Imp(assumption.expression,e)) @: position)(premise.conclusion)
}

class ImpElimC(val leftPremise:NaturalDeductionProof, val rightPremise:NaturalDeductionProof, 
               val leftPosition: Position, val rightPosition: Position, val arrow: ImpElimCArrow)
extends NaturalDeductionProof("ImpElim", leftPremise::rightPremise::Nil) {
  require(leftPosition isPositiveIn leftPremise.conclusion)
  require(rightPosition isPositiveIn rightPremise.conclusion)
  override lazy val context = leftPremise.context ++ rightPremise.context
  private def deepAuxL = leftPremise.conclusion !: leftPosition 
  private def deepAuxR = rightPremise.conclusion !: rightPosition;
  private def deepMain = (deepAuxL,deepAuxR) match {
    case (a,Imp(b,c)) if a == b => c
    case _ => throw new Exception("Implication Elimination Rule cannot be applied because the formulas do not match")
  }
  override val conclusion = arrow match {
    case RightArrow => (((_:E) => (((_:E) => deepMain) @: rightPosition)(rightPremise.conclusion)) @: leftPosition)(leftPremise.conclusion)
    case LeftArrow  => (((_:E) => (((_:E) => deepMain) @: leftPosition)(leftPremise.conclusion)) @: rightPosition)(rightPremise.conclusion)
  }
}
