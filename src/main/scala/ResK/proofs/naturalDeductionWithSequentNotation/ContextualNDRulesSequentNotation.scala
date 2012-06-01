package ResK.proofs.naturalDeductionWithSequentNotation

import ResK.judgments.Sequent
import ResK.expressions.E
import ResK.formulas._
import ResK.positions._
import ResK.proofs.{SequentProof,NoImplicitContraction,ImplicitContraction,SingleMainFormula,Right}
//import ResK.provers.InferenceRule
import typeAliases._


class ImpIntroC(val premise: SequentProof, val auxL: E, val position: Position) 
extends NaturalDeductionProof("ImpIntroC",premise::Nil, Map(premise -> Sequent(auxL,premise.conclusion.suc.head)))
with SingleMainFormula with Right with NoImplicitContraction {
  require(position isPositiveIn premise.conclusion.suc.head)
  override val mainFormula = (((e:E) => Imp(auxL,e)) @: position)(premise.conclusion.suc.head)
}

sealed abstract class ImpElimCArrow
case object RightArrow extends ImpElimCArrow
case object LeftArrow extends ImpElimCArrow

class ImpElimC(val leftPremise: SequentProof, val rightPremise: SequentProof, 
               val leftPosition: Position, val rightPosition: Position, val arrow: ImpElimCArrow)
extends NaturalDeductionProof("ImpElimC"+arrow, leftPremise::rightPremise::Nil,
                     Map(leftPremise -> Sequent(Nil,leftPremise.conclusion.suc.head), rightPremise -> Sequent(Nil,rightPremise.conclusion.suc.head)))
with ImplicitContraction with SingleMainFormula with Right  {
  def auxL = leftPremise.conclusion.suc.head; def auxR = rightPremise.conclusion.suc.head;
  require((leftPosition isPositiveIn auxL) && (rightPosition isPositiveIn auxR))
  
  val deepAuxL = auxL !: leftPosition; val deepAuxR = auxR !: rightPosition;
  
  val deepMain = (deepAuxL,deepAuxR) match {
    case (a,Imp(b,c)) if a == b => c
    case _ => throw new Exception("Implication Elimination Rule cannot be applied because the formulas do not match")
  }
  
  override val mainFormula = arrow match {
    case RightArrow => (((_:E) => (((_:E) => deepMain) @: rightPosition)(auxR)) @: leftPosition)(auxL)
    case LeftArrow  => (((_:E) => (((_:E) => deepMain) @: leftPosition)(auxL)) @: rightPosition)(auxR)
  }
}

// ToDo: Companion Objects