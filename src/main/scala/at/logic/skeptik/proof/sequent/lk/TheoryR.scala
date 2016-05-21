package at.logic.skeptik.proof
package sequent
package lk

import at.logic.skeptik.expression._

class TheoryR(override val leftPremise:SequentProofNode, 
              override val rightPremise:SequentProofNode, 
              override val auxL:E, 
              override val auxR:E) 
extends R(leftPremise, rightPremise, auxL, auxR) 

object TheoryR extends RCompanion[TheoryR] {
  protected def create(leftPremise:SequentProofNode, rightPremise:SequentProofNode, auxL:E, auxR:E) = 
    new TheoryR(leftPremise:SequentProofNode, rightPremise:SequentProofNode, auxL:E, auxR:E)
  
  def unapply(p: SequentProofNode) = p match {
    case p: TheoryR => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}

