package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression.E


// The following class uses the methods from trait ImplicitContraction for computing the formula ancestor relation. 
// This turned out to produce too many sequents, preventing its use in propositional proof compression,
// where the ancestor relation is irrelevant anyway.
//class CutIC(val leftPremise:SequentProofNode, val rightPremise:SequentProofNode, val auxL:E, val auxR:E)
//extends AbstractCut with ImplicitContraction 

// This class replaces the inefficient class above. It is a quick fix. 
// It simply does not compute the ancestor relation.
// ToDo: This class should eventually use SetSequent instead of SeqSequent.
class CutIC(val leftPremise:SequentProofNode, val rightPremise:SequentProofNode, val auxL:E, val auxR:E) 
extends AbstractCut {
  // Requirements only necessary because I commented out the inefficient requirement in SequentProofNode 
  require(leftPremise.conclusion.suc contains auxL)
  require(rightPremise.conclusion.ant contains auxR)
  
  override def ancestry(f: E, premise: SequentProofNode): Sequent = throw new Exception("Not implemented")
  override def activeAncestry(f: E, premise: SequentProofNode): Sequent = throw new Exception("Not implemented")
  override def contextAncestry(f: E, premise: SequentProofNode): Sequent = throw new Exception("Not implemented")
  override def auxFormulasMap: Map[SequentProofNode, Sequent] = throw new Exception("Not implemented")
  override def mainFormulas : Sequent = throw new Exception("Not implemented")
  override def conclusionContext : Sequent = throw new Exception("Not implemented")

  // ToDo: if necessary, this could be made more efficient by making 
  // our own implementation of filterNot, with early breaking of the traversal, 
  // because we know that auxR occurs only once in the rightPremise.conclusion.ant, for example.
  // Similarly, distinct could be optimized.
  // But unless there is immediate need for this, I would rather leave this as it is, 
  // because anyway a lot will change when SetSequent is used. 
  override lazy val conclusion: Sequent = 
    new Sequent((leftPremise.conclusion.ant ++ (rightPremise.conclusion.ant.filterNot(_ eq auxR))).distinct,
                (rightPremise.conclusion.suc ++ (leftPremise.conclusion.suc.filterNot(_ eq auxL))).distinct)
}


object CutIC {
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, auxL:E, auxR:E) = new CutIC(leftPremise,rightPremise,auxL,auxR)
  
  def apply(leftPremise: SequentProofNode, 
            rightPremise: SequentProofNode, 
            isPivot: E => Boolean,
            returnPremiseOnfailure: Boolean = false,
            choosePremise: ((SequentProofNode, SequentProofNode) => SequentProofNode) = (l,r) => l) = 
    (leftPremise.conclusion.suc.find(isPivot), rightPremise.conclusion.ant.find(isPivot)) match {
      case (Some(auxL), Some(auxR)) => new CutIC(leftPremise, rightPremise, auxL, auxR)
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
      case Some((auxL,auxR)) => new CutIC(premise1,premise2,auxL,auxR)
      case None => findPivots(premise2,premise1) match {
        case Some((auxL,auxR)) => new CutIC(premise2,premise1,auxL,auxR)
        case None => throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
      }
    }
  }
  def unapply(p: SequentProofNode) = p match {
    case p: CutIC => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}