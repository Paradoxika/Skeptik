package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._

// ToDo: This class should eventually use SetSequent instead of SeqSequent.
class R(val leftPremise:SequentProofNode, val rightPremise:SequentProofNode, val auxL:E, val auxR:E) 
extends AbstractCut {
  // Requirements only necessary because inefficient requirement in SequentProofNode was commented out 
  require(leftPremise.conclusion.suc contains auxL)
  require(rightPremise.conclusion.ant contains auxR)
  
  override def auxFormulasMap = Map(leftPremise -> Sequent()(auxL),
                                    rightPremise -> Sequent(auxR)())    
  
  override def mainFormulas : Sequent = Sequent()()
  override def conclusionContext : Sequent = conclusion

  override lazy val conclusion: Sequent = 
    new Sequent((leftPremise.conclusion.ant ++ (rightPremise.conclusion.ant.filterNot(_ eq auxR))).distinct,
                (rightPremise.conclusion.suc ++ (leftPremise.conclusion.suc.filterNot(_ eq auxL))).distinct)
}

object R extends RCompanion[R] {
  protected def create(leftPremise:SequentProofNode, rightPremise:SequentProofNode, auxL:E, auxR:E) = 
    new R(leftPremise:SequentProofNode, rightPremise:SequentProofNode, auxL:E, auxR:E)
  
  def unapply(p: SequentProofNode) = p match {
    case p: R => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}

abstract class RCompanion[+T <: R] {
  protected def create(leftPremise:SequentProofNode, rightPremise:SequentProofNode, auxL:E, auxR:E): T
  
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, auxL:E, auxR:E) = create(leftPremise,rightPremise,auxL,auxR)
  
  def apply(leftPremise: SequentProofNode, 
            rightPremise: SequentProofNode, 
            pivot: E,
            returnPremiseOnfailure: Boolean = false,
            choosePremise: ((SequentProofNode, SequentProofNode) => SequentProofNode) = (l,r) => if (l.conclusion.width < r.conclusion.width) l else r ) = 
    (leftPremise.conclusion.suc.find(_ == pivot), rightPremise.conclusion.ant.find(_ == pivot)) match {
      case (Some(auxL), Some(auxR)) => create(leftPremise, rightPremise, auxL, auxR)
      case (None, Some(auxR)) if returnPremiseOnfailure => leftPremise
      case (Some(auxL), None) if returnPremiseOnfailure => rightPremise
      case (None, None) if returnPremiseOnfailure => choosePremise(leftPremise, rightPremise)
      case _ => throw new Exception("Auxiliary formulas not found.\n"+leftPremise.conclusion + "\n" + rightPremise.conclusion + "\n" + pivot)
    } 
  
  def apply(premise1:SequentProofNode, premise2:SequentProofNode) = {
    def findPivots(p1:SequentProofNode, p2:SequentProofNode): Option[(E,E)] = {
      for (auxL <- p1.conclusion.suc; auxR <- p2.conclusion.ant) if (auxL == auxR) return Some(auxL,auxR)
      return None
    }
    findPivots(premise1,premise2) match {
      case Some((auxL,auxR)) => {
        create(premise1,premise2,auxL,auxR)
      }
      case None => findPivots(premise2,premise1) match {
        case Some((auxL,auxR)) => create(premise2,premise1,auxL,auxR)
        case None => {
          throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
        }
      }
    }
  }

}
