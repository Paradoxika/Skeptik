package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression.E

// ToDo: This class should eventually use SetSequent instead of SeqSequent.
class R(val leftPremise:SequentProofNode, val rightPremise:SequentProofNode, val auxL:E, val auxR:E) 
extends AbstractCut {
  // Requirements only necessary because inefficient requirement in SequentProofNode was commented out 
  require(leftPremise.conclusion.suc contains auxL)
  require(rightPremise.conclusion.ant contains auxR)
  
  override def auxFormulasMap = Map(leftPremise -> Sequent()(auxL),
                                    rightPremise -> Sequent(auxR)())    
  
  //override def auxFormulasMap: Map[SequentProofNode, Sequent] = throw new Exception("Not implemented")
  override def mainFormulas : Sequent = Sequent()()
  override def conclusionContext : Sequent = conclusion

  override lazy val conclusion: Sequent = 
    new Sequent((leftPremise.conclusion.ant ++ (rightPremise.conclusion.ant.filterNot(_ eq auxR))).distinct,
                (rightPremise.conclusion.suc ++ (leftPremise.conclusion.suc.filterNot(_ eq auxL))).distinct)
}


object R {
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, auxL:E, auxR:E) = new R(leftPremise,rightPremise,auxL,auxR)
  
  def apply(leftPremise: SequentProofNode, 
            rightPremise: SequentProofNode, 
            isPivot: E => Boolean,
            returnPremiseOnfailure: Boolean = false,
            choosePremise: ((SequentProofNode, SequentProofNode) => SequentProofNode) = (l,r) => l) = 
    (leftPremise.conclusion.suc.find(isPivot), rightPremise.conclusion.ant.find(isPivot)) match {
      case (Some(auxL), Some(auxR)) => new R(leftPremise, rightPremise, auxL, auxR)
      case (None, Some(auxR)) if returnPremiseOnfailure => leftPremise
      case (Some(auxL), None) if returnPremiseOnfailure => rightPremise
      case (None, None) if returnPremiseOnfailure => choosePremise(leftPremise, rightPremise)
      case _ => throw new Exception("Auxiliary formulas not found.")
    } 
  
  def apply(premise1:SequentProofNode, premise2:SequentProofNode) = {
    def findPivots(p1:SequentProofNode, p2:SequentProofNode): Option[(E,E)] = {
      for (auxL <- p1.conclusion.suc; auxR <- p2.conclusion.ant) if (auxL == auxR) return Some(auxL,auxR)
      return None
    }
    findPivots(premise1,premise2) match {
      case Some((auxL,auxR)) => new R(premise1,premise2,auxL,auxR)
      case None => findPivots(premise2,premise1) match {
        case Some((auxL,auxR)) => new R(premise2,premise1,auxL,auxR)
        case None => throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
      }
    }
  }
  def unapply(p: SequentProofNode) = p match {
    case p: R => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}