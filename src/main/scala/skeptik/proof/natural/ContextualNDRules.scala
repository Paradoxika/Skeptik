package skeptik.proof.natural

import skeptik.expression.E
import skeptik.expression.formula.Imp
import skeptik.expression.formula.position.{IntListPosition => Position,EmptyP}
import skeptik.prover.InferenceRule
import skeptik.judgment.{NaturalSequent,NamedE}

// TODO: Add Intuitionistic Soundness Condition

sealed abstract class ImpElimCArrow
case object RightArrow extends ImpElimCArrow
case object LeftArrow extends ImpElimCArrow

class ImpIntroC(val premise: NaturalDeductionProof, val assumption: NamedE, val position: Position)
extends NaturalDeductionProof("ImpIntroC",premise::Nil) {
  require(premise.conclusion.context contains assumption)
  require(position isPositiveIn premise.conclusion.e)
  override val conclusion = new NaturalSequent(premise.conclusion.context - assumption , (((e:E) => Imp(assumption.expression,e)) @: position)(premise.conclusion.e))
}

class ImpElimC(val leftPremise: NaturalDeductionProof, val rightPremise: NaturalDeductionProof, 
               val leftPosition: Position, val rightPosition: Position, val arrow: ImpElimCArrow)
extends NaturalDeductionProof("ImpElimC", leftPremise::rightPremise::Nil) {
  require(leftPosition isPositiveIn leftPremise.conclusion.e)
  require(rightPosition isPositiveIn rightPremise.conclusion.e)
  private def deepAuxL = (leftPremise.conclusion.e !: leftPosition).get 
  private def deepAuxR = (rightPremise.conclusion.e !: rightPosition).get
  private def deepMain = (deepAuxL,deepAuxR) match {
    case (a,Imp(b,c)) if a == b => c
    case _ => throw new Exception("Implication Elimination Rule cannot be applied because the formulas do not match")
  }
  private def main = arrow match {
    case RightArrow => (((_:E) => (((_:E) => deepMain) @: rightPosition)(rightPremise.conclusion.e)) @: leftPosition)(leftPremise.conclusion.e)
    case LeftArrow  => (((_:E) => (((_:E) => deepMain) @: leftPosition)(leftPremise.conclusion.e)) @: rightPosition)(rightPremise.conclusion.e)
  }
  val conclusion = new NaturalSequent(leftPremise.conclusion.context ++ rightPremise.conclusion.context, main)
}

object ImpIntroC extends InferenceRule[NaturalSequent, NaturalDeductionProof] {
  def apply(premise: NaturalDeductionProof, assumption: NamedE, position: Position) = new ImpIntroC(premise, assumption, position)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpIntroC => Some((p.premise, p.assumption, p.position))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent): Seq[Seq[NaturalSequent]] = {
    val positivePositions = EmptyP.getSubpositions(j.e).filter(_.isPositiveIn(j.e))
    val seen = new scala.collection.mutable.HashSet[E]
    (for (p <- positivePositions) yield {
      val deepMain = (j.e !: p).get
      deepMain match {
        case Imp(a,deepAux) => {
          val subGoal = (((_:E)=>deepAux) @: p)(j.e)
          if (seen contains subGoal) None
          else {
            seen += subGoal
            Some(Seq(new NaturalSequent(j.context + NamedE(nameFactory(), a),  subGoal )))
          } 
        } 
        case _ => None
      }      
    }).filter(_ != None).map(_.get)
  }
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: NaturalSequent): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 1) {
      val positions = EmptyP.getSubpositions(conclusion.e)
      val positivePositions = positions.filter(p => p.isPositiveIn(conclusion.e) && p.existsIn(premises(0).conclusion.e) && p.isPositiveIn(premises(0).conclusion.e))
      val optionProofs = (for (p <- positivePositions) yield {
        val deepMain = (conclusion.e !: p).get
        deepMain match {
          case i @ Imp(a,b) => {
            val deepAux = (premises(0).conclusion.e !: p).get
            if (b == deepAux) premises(0).conclusion.context.find(_.expression == a) match {
              case Some(assumption) => Some(new ImpIntroC(premises(0), assumption, p))
              case None => None
            }
            else None   
          }
          case _ => None
        }
      })
      optionProofs.find(_ != None).getOrElse(None)
    }
    else None
  }
}


object ImpElimC extends InferenceRule[NaturalSequent, NaturalDeductionProof] {
  def apply(leftPremise: NaturalDeductionProof, rightPremise: NaturalDeductionProof, leftPosition: Position, rightPosition: Position, arrow: ImpElimCArrow) = 
    new ImpElimC(leftPremise, rightPremise, leftPosition, rightPosition, arrow)
  
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpElimC => Some((p.leftPremise, p.rightPremise, p.leftPosition, p.rightPosition, p.arrow))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent): Seq[Seq[NaturalSequent]] = {
    val outerPositions = EmptyP.getSubpositions(j.e).filter(_.isPositiveIn(j.e))
    var result: Seq[Seq[NaturalSequent]] = Seq()
    
    for (outP <- outerPositions) {
      val semiDeepMain = (j.e !: outP).get
      val innerPositions = EmptyP.getSubpositions(semiDeepMain).filter(_.isPositiveIn(semiDeepMain))
      for (inP <- innerPositions) {
        val deepMain = (semiDeepMain !: inP).get
        for (n <- j.context) {
          val auxR = n.expression
          def computeSubGoals(leftP: Position, rightP: Position, auxLBase: E) = {
            val deepAuxR = (auxR !: rightP).get 
            deepAuxR match {
              case Imp(a,b) if b == deepMain => {
                
                val bOccursPositivelyInA = EmptyP.getSubpositions(a).filter(p => p.isPositiveIn(a) && (a !: p).get == b).length > 0
                
                if (!bOccursPositivelyInA) {
                  val auxL = (((_:E) => a) @: leftP)(auxLBase)
                  result = result :+ Seq(new NaturalSequent(j.context,auxL), new NaturalSequent(j.context,auxR))
                }
              }
              case _ => 
            }
          }
            
          if (inP existsIn auxR) computeSubGoals(outP, inP, j.e)

          if (outP existsIn auxR) computeSubGoals(inP, outP, semiDeepMain)

        }
      }
    }
    result
  }
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: NaturalSequent): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 2) {
      val auxL = premises(0).conclusion.e
      val auxR = premises(1).conclusion.e
      
      
      val positionsR = EmptyP.getSubpositions(auxR).filter(_ isPositiveIn auxR)
      
      val proofs: Seq[NaturalDeductionProof] = (for (posR <- positionsR) yield (auxR !: posR).get match {
        case Imp(a,b) => {
          val positionsL = EmptyP.getSubpositions(auxL).filter(pos => (pos isPositiveIn auxL) && (auxL !: pos).get == a)
          for (posL <- positionsL) yield Seq(ImpElimC(premises(0), premises(1), posL, posR, LeftArrow), 
                                             ImpElimC(premises(0), premises(1), posL, posR, RightArrow)) 

        }
        case _ => Seq()
      }).flatten.flatten
      proofs.find(_.conclusion == conclusion)
    }
    else None
  }
}