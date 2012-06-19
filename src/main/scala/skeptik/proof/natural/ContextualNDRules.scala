package skeptik.proof.natural

import skeptik.expression.E
import skeptik.expression.formula.Imp
import skeptik.expression.formula.position.{IntListP => Position,EmptyP}
import skeptik.prover.InferenceRuleWithSideEffects
import typeAliases._

// ToDo: Add Intuitionistic Soundness Condition

sealed abstract class ImpElimCArrow
case object RightArrow extends ImpElimCArrow
case object LeftArrow extends ImpElimCArrow

class ImpIntroC(val premise: NaturalDeductionProof, val assumption: NamedE, val position: Position)
extends NaturalDeductionProof("ImpIntroC",premise::Nil) {
  require(premise.context contains assumption)
  require(position isPositiveIn premise.conclusion)
  override val context = premise.context - assumption
  override val conclusion = (((e:E) => Imp(assumption.expression,e)) @: position)(premise.conclusion)
}

class ImpElimC(val leftPremise: NaturalDeductionProof, val rightPremise: NaturalDeductionProof, 
               val leftPosition: Position, val rightPosition: Position, val arrow: ImpElimCArrow)
extends NaturalDeductionProof("ImpElimC", leftPremise::rightPremise::Nil) {
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

object ImpIntroC extends InferenceRuleWithSideEffects[E, NaturalDeductionProof, Context] {
  def apply(premise: NaturalDeductionProof, assumption: NamedE, position: Position) = new ImpIntroC(premise, assumption, position)
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpIntroC => Some((p.premise, p.assumption, p.position))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: E)(implicit c: Context): Seq[Seq[(Context,E)]] = {
    val positivePositions = new EmptyP().getSubpositions(j).filter(_.isPositiveIn(j))
    val seen = new scala.collection.mutable.HashSet[E]
    (for (p <- positivePositions) yield {
      val deepMain = j !: p
      deepMain match {
        case i @ Imp(a,deepAux) => {
          val subGoal = (((_:E)=>deepAux) @: p)(j)
          if (seen contains subGoal) None
          else {
            seen += subGoal
            Some(Seq((c + NamedE(nameFactory(), a),  subGoal )))
          } 
        } 
        case _ => None
      }      
    }).filter(_ != None).map(r => r.get)
  }
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: E)(implicit c: Context): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 1) {
      val positions = new EmptyP().getSubpositions(conclusion)
      val positivePositions = positions.filter(p => p.isPositiveIn(conclusion) && p.existsIn(premises(0).conclusion) && p.isPositiveIn(premises(0).conclusion))
      val optionProofs = (for (p <- positivePositions) yield {
        val deepMain = conclusion !: p
        deepMain match {
          case i @ Imp(a,b) => {
            val deepAux = premises(0).conclusion !: p
            if (b == deepAux) premises(0).context.find(_.expression == a) match {
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


object ImpElimC extends InferenceRuleWithSideEffects[E, NaturalDeductionProof, Context] {
  def apply(leftPremise: NaturalDeductionProof, rightPremise: NaturalDeductionProof, leftPosition: Position, rightPosition: Position, arrow: ImpElimCArrow) = 
    new ImpElimC(leftPremise, rightPremise, leftPosition, rightPosition, arrow)
  
  def unapply(p: NaturalDeductionProof) = p match {
    case p: ImpElimC => Some((p.leftPremise, p.rightPremise, p.leftPosition, p.rightPosition, p.arrow))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: E)(implicit c: Context): Seq[Seq[(Context,E)]] = {
    val outerPositions = new EmptyP().getSubpositions(j).filter(_.isPositiveIn(j))
    var result: Seq[Seq[(Context,E)]] = Seq()
    
    for (outP <- outerPositions) {
      val semiDeepMain = j !: outP
      val innerPositions = new EmptyP().getSubpositions(semiDeepMain).filter(_.isPositiveIn(semiDeepMain))
      for (inP <- innerPositions) {
        val deepMain = semiDeepMain !: inP
        for (n <- c) {
          val auxR = n.expression
          def computeSubGoals(leftP: Position, rightP: Position, auxLBase: E) = {
            val deepAuxR = auxR !: rightP 
            deepAuxR match {
              case Imp(a,b) if b == deepMain => {
                
                val bOccursPositivelyInA = (new EmptyP).getSubpositions(a).filter(p => p.isPositiveIn(a) && (a !: p) == b).length > 0
                
                if (!bOccursPositivelyInA) {
                  val auxL = (((_:E) => a) @: leftP)(auxLBase)
                  result = result :+ Seq((c,auxL),(c,auxR))
                }
              }
              case _ => 
            }
          }
            
          if (inP existsIn auxR) computeSubGoals(outP, inP, j)

          if (outP existsIn auxR) computeSubGoals(inP, outP, semiDeepMain)

        }
      }
    }
    result
  }
  
  def apply(premises: Seq[NaturalDeductionProof], conclusion: E)(implicit c: Context): Option[NaturalDeductionProof] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 2) {
      val auxL = premises(0).conclusion
      val auxR = premises(1).conclusion
      
      
      val positionsR = new EmptyP().getSubpositions(auxR).filter(_ isPositiveIn auxR)
      
      val proofs: Seq[NaturalDeductionProof] = (for (posR <- positionsR) yield (auxR !: posR) match {
        case Imp(a,b) => {
          val positionsL = new EmptyP().getSubpositions(auxL).filter(pos => (pos isPositiveIn auxL) && (auxL !: pos) == a)
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