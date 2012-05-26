package ResK.proofs.naturalDeductionWithSequentNotation

import ResK.judgments.Sequent
import ResK.expressions.E
import ResK.formulas._
import ResK.positions._
import ResK.proofs.{SequentProof,NoImplicitContraction,ImplicitContraction,SingleMainFormula,Right}
import ResK.provers.InferenceRule
import typeAliases._


class ImpIntroC(val premise: SequentProof, val auxL: E, val position: Position) 
extends NaturalDeductionProof("ImpIntroC",premise::Nil, Map(premise -> Sequent(auxL,premise.conclusion.suc.head)))
with SingleMainFormula with Right with NoImplicitContraction {
  require(position isPositiveIn premise.conclusion.suc.head)
  override val mainFormula = (((e:E) => Imp(auxL,e)) @: position)(premise.conclusion.suc.head)
}

class ImpElimC(val leftPremise: SequentProof, val rightPremise: SequentProof, val leftPosition: Position, val rightPosition: Position)
extends NaturalDeductionProof("ImpElimC", leftPremise::rightPremise::Nil,
                     Map(leftPremise -> Sequent(Nil,leftPremise.conclusion.suc.head), rightPremise -> Sequent(Nil,rightPremise.conclusion.suc.head)))
with ImplicitContraction with SingleMainFormula with Right  {
  val leftC = leftPremise.conclusion.suc.head
  val rightC = rightPremise.conclusion.suc.head
  require(leftPosition isPositiveIn leftC)
  require(rightPosition isPositiveIn rightC)
  val deepLeftC = leftC !: leftPosition
  val deepRightC = rightC !: rightPosition
  val deepMain = (deepLeftC,deepRightC) match {
    case (a,Imp(b,c)) if a == b => c
    case _ => throw new Exception("Implication Elimination Rule cannot be applied because the formulas do not match")
  }
  
  override val mainFormula = (((_:E) => (((_:E) => deepMain) @: rightPosition)(rightC)) @: leftPosition)(leftC)
}

// ToDo: Companion Objects