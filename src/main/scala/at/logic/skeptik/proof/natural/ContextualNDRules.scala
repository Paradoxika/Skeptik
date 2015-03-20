package at.logic.skeptik.proof
package natural

import at.logic.skeptik.expression.E
import at.logic.skeptik.expression.formula.Imp
import at.logic.skeptik.expression.formula.position.{IntListPosition => Position,EmptyP}
import at.logic.skeptik.prover.InferenceRule
import at.logic.skeptik.judgment.{NaturalSequent,NamedE}



sealed abstract class ImpElimCArrow
case object RightArrow extends ImpElimCArrow
case object LeftArrow extends ImpElimCArrow


class ImpIntroCK(val premise: NaturalDeductionProofNode, val assumption: NamedE, val position: Position)
extends NaturalDeductionProofNode with Unary {
  require(premise.conclusion.context contains assumption)
  require(position isPositiveIn premise.conclusion.e)
  override val conclusion = new NaturalSequent(premise.conclusion.context - assumption , (((e:E) => Imp(assumption.expression,e)) @: position)(premise.conclusion.e))
}

class ImpIntroC(premise: NaturalDeductionProofNode, assumption: NamedE, position: Position)
extends ImpIntroCK(premise, assumption, position)
with SoundnessCondition

trait SoundnessCondition extends ImpIntroCK { 
  def assumptionIsUsed: Boolean = {
    def rec(p: NaturalDeductionProofNode): Boolean = p match {
      case Assumption(context, a) => if (a == assumption) true else false
      case _ => p.premises.exists(premise => rec(premise))
    }
    rec(this)
  }
  require( (position isStronglyPositiveIn conclusion.e) || !assumptionIsUsed)
}

class ImpElimC(val leftPremise: NaturalDeductionProofNode, val rightPremise: NaturalDeductionProofNode, 
               val leftPosition: Position, val rightPosition: Position, val arrow: ImpElimCArrow)
extends NaturalDeductionProofNode with Binary {
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

abstract class ImpIntroCRule extends InferenceRule[NaturalSequent, NaturalDeductionProofNode] {
  def apply(premise: NaturalDeductionProofNode, assumption: NamedE, position: Position): NaturalDeductionProofNode
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent): Seq[Seq[NaturalSequent]] = {
    val stronglyPositivePositions = EmptyP.getSubpositions(j.e).filter(_.isStronglyPositiveIn(j.e))
    
    val seen = new collection.mutable.HashSet[E]
    (for (p <- stronglyPositivePositions) yield {
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
  
  def apply(premises: Seq[NaturalDeductionProofNode], conclusion: NaturalSequent): Option[NaturalDeductionProofNode] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    //println("!!! Trying to reconstruct : " + conclusion )
    //println("!!! from " + premises)
    //println()
    
    if (premises.length == 1) {
      val positions = EmptyP.getSubpositions(conclusion.e)
      //println("!!! positions: " +  positions)
      val positivePositions = positions.filter(p => p.isPositiveIn(conclusion.e) && p.existsIn(premises(0).conclusion.e) && p.isPositiveIn(premises(0).conclusion.e))
      //println("!!! positive positions: " +  positivePositions)
      
      val optionProofNodes = (for (p <- positivePositions.view) yield {
        val deepMain = (conclusion.e !: p).get
        
        //println("    !!! p: " + p)
        //println("    !!! deepMain: " + deepMain)
        deepMain match {
          case i @ Imp(a,b) => {
            val deepAux = (premises(0).conclusion.e !: p).get
            //println("    !!! deepAux: " + deepAux)
            //println("    !!! b: " + b)
            if (b == deepAux) {
              val ass = premises(0).conclusion.context.find(_.expression == a) 
              //println("    !!! a: " + a)
              //println("    !!! ass: " + ass)
              ass match {
                case Some(assumption) => try {
                  //println("    !!! before ")
                  val r = Some(apply(premises(0), assumption, p)) 
                  //println("    !!! after ")
                  r
                } catch {
                  case e: Throwable => {
                    //println(e)
                    None 
                  }
                }
                case None => None
              }
            }
            else None   
          }
          case _ => None
        }
      })
      optionProofNodes.find(_ != None).getOrElse(None)
    }
    else None
  }
}

object ImpIntroC extends ImpIntroCRule {
  def apply(premise: NaturalDeductionProofNode, assumption: NamedE, position: Position) = new ImpIntroC(premise, assumption, position)
  def unapply(p: NaturalDeductionProofNode) = p match {
    case p: ImpIntroC => Some((p.premise, p.assumption, p.position))
    case _ => None
  }
}

object ImpIntroCK extends ImpIntroCRule {
  def apply(premise: NaturalDeductionProofNode, assumption: NamedE, position: Position) = new ImpIntroCK(premise, assumption, position)
  def unapply(p: NaturalDeductionProofNode) = p match {
    case p: ImpIntroCK => Some((p.premise, p.assumption, p.position))
    case _ => None
  }
}


object ImpElimC extends InferenceRule[NaturalSequent, NaturalDeductionProofNode] 
with DeepMatch {
  def apply(leftPremise: NaturalDeductionProofNode, rightPremise: NaturalDeductionProofNode, leftPosition: Position, rightPosition: Position, arrow: ImpElimCArrow) = 
    new ImpElimC(leftPremise, rightPremise, leftPosition, rightPosition, arrow)
  
  def unapply(p: NaturalDeductionProofNode) = p match {
    case p: ImpElimC => Some((p.leftPremise, p.rightPremise, p.leftPosition, p.rightPosition, p.arrow))
    case _ => None
  }
  
  // applies the rule bottom-up: given a conclusion judgment, returns a sequence of possible premise judgments.
  def apply(j: NaturalSequent): Seq[Seq[NaturalSequent]] = {
    var result: Seq[Seq[NaturalSequent]] = Seq()
    //println("j: " + j)
    
    
    val outerPositions = EmptyP.getSubpositions(j.e).filter(_.isPositiveIn(j.e))
    //println("!!! outerPositions: " + outerPositions )
    
    for (outP <- outerPositions) {
      val semiDeepMain = (j.e !: outP).get
      //println("  !!! outP: " + outP )
      //println("  !!! semiDeepMain: " + semiDeepMain )
      
      val innerPositions = EmptyP.getSubpositions(semiDeepMain).filter(_.isPositiveIn(semiDeepMain))
      //println("  !!! innerPositions: " + innerPositions )
      
      for (inP <- innerPositions) {
        val deepMain = (semiDeepMain !: inP).get
        
        //println("    !!! inP: " + inP )
        //println("    !!! deepMain: " + deepMain )
        
        for (n <- j.context) {
          val futureAuxR = n.expression
          //println("      !!! futureAuxR: " + futureAuxR )
          def computeSubGoals(leftP: Position, rightP: Position, auxLBase: E, auxRBase: E) = {
            val futureDeepAuxR = (futureAuxR !: rightP).get 
            //println("      !!! futureDeepAuxR: " + futureDeepAuxR )
            
            deepMatch(futureDeepAuxR,deepMain) match {
              case Some(deepAuxR @ Imp(a,b)) => {
                //println("      !!! auxLBase: " + auxLBase)
                //println("      !!! auxRBase: " + auxRBase)
                val auxL = (((_:E) => a) @: leftP)(auxLBase)
                val auxR = (((_:E) => deepAuxR) @: rightP)(auxRBase)
                result = result :+ Seq(new NaturalSequent(j.context,auxL), new NaturalSequent(Set(n),auxR))
              }
              case _ => 
            }
            
            
//            deepAuxR match {
//              // ToDo: This is incomplete. A deep match must be done. 
//              case Imp(a,b) if b == deepMain => {
//                //println("      !!! match!"  )
//                //val bOccursPositivelyInA = EmptyP.getSubpositions(a).filter(p => p.isPositiveIn(a) && (a !: p).get == b).length > 0
//                
//                //println("      !!! bOccursPositivelyInA : " + bOccursPositivelyInA)
//                //if (bOccursPositivelyInA) {
//                  val auxL = (((_:E) => a) @: leftP)(auxLBase)
//                  //println("      !!! auxL: " + auxL )
//                  result = result :+ Seq(new NaturalSequent(j.context,auxL), new NaturalSequent(Set(n),auxR))
//                //}
//              }
//              case _ => 
//            }
          }
          //println(" =====  inP existsIn AuxR ====== ")  
          if (inP existsIn futureAuxR) computeSubGoals(outP, inP, j.e, semiDeepMain)

          //println(" =====  outP existsIn AuxR ====== ")
          if (outP existsIn futureAuxR) computeSubGoals(inP, outP, semiDeepMain, j.e)

        }
      }
    }
    result
  }
  
//  def apply(j: NaturalSequent): Seq[Seq[NaturalSequent]] = {
//    var result: Seq[Seq[NaturalSequent]] = Seq()
//    
//    val outerPositions = EmptyP.getSubpositions(j.e).filter(_.isPositiveIn(j.e))
//    //println("!!! outerPositions: " + outerPositions )
//    
//    for (outP <- outerPositions) {
//      val semiDeepMain = (j.e !: outP).get
//      //println("  !!! outP: " + outP )
//      //println("  !!! semiDeepMain: " + semiDeepMain )
//      
//      val innerPositions = EmptyP.getSubpositions(semiDeepMain).filter(_.isPositiveIn(semiDeepMain))
//      //println("  !!! innerPositions: " + innerPositions )
//      
//      for (inP <- innerPositions) {
//        val deepMain = (semiDeepMain !: inP).get
//        
//        //println("    !!! inP: " + inP )
//        //println("    !!! deepMain: " + deepMain )
//        
//        for (n <- j.context) {
//          val auxR = n.expression
//          //println("      !!! auxR: " + auxR )
//          def computeSubGoals(leftP: Position, rightP: Position, auxLBase: E) = {
//            val deepAuxR = (auxR !: rightP).get 
//            //println("      !!! deepAuxR: " + deepAuxR )
//           
//            
//            
//            deepAuxR match {
//              // ToDo: This is incomplete. A deep match must be done. 
//              case Imp(a,b) if b == deepMain => {
//                //println("      !!! match!"  )
//                //val bOccursPositivelyInA = EmptyP.getSubpositions(a).filter(p => p.isPositiveIn(a) && (a !: p).get == b).length > 0
//                
//                //println("      !!! bOccursPositivelyInA : " + bOccursPositivelyInA)
//                //if (bOccursPositivelyInA) {
//                  val auxL = (((_:E) => a) @: leftP)(auxLBase)
//                  //println("      !!! auxL: " + auxL )
//                  result = result :+ Seq(new NaturalSequent(j.context,auxL), new NaturalSequent(Set(n),auxR))
//                //}
//              }
//              case _ => 
//            }
//          }
//          //println(" =====  inP existsIn AuxR ====== ")  
//          if (inP existsIn auxR) computeSubGoals(outP, inP, j.e)
//
//          //println(" =====  outP existsIn AuxR ====== ")
//          if (outP existsIn auxR) computeSubGoals(inP, outP, semiDeepMain)
//
//        }
//      }
//    }
//    result
//  }
  
  def apply(premises: Seq[NaturalDeductionProofNode], conclusion: NaturalSequent): Option[NaturalDeductionProofNode] = { // applies the rule top-down: given premise proofs, tries to create a proof of the given conclusion.
    if (premises.length == 2) {
      val auxL = premises(0).conclusion.e
      val auxR = premises(1).conclusion.e
      
      val positionsR = EmptyP.getSubpositions(auxR).filter(_ isPositiveIn auxR)
      
      val proofs = (for (posR <- positionsR.view) yield (auxR !: posR).get match {
        case Imp(a,b) => {
          val positionsL = EmptyP.getSubpositions(auxL).filter(pos => (pos isPositiveIn auxL) && (auxL !: pos).get == a)
          for (posL <- positionsL.view) yield Seq(ImpElimC(premises(0), premises(1), posL, posR, LeftArrow), 
                                             ImpElimC(premises(0), premises(1), posL, posR, RightArrow)) 

        }
        case _ => Seq()
      }).flatten.flatten
      proofs.find(_.conclusion == conclusion)
    }
    else None
  }
}