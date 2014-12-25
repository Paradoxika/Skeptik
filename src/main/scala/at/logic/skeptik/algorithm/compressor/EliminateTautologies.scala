package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.{Axiom, R}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}


object EliminateTautologies 
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {
  def isTautology(s: Sequent) = s.ant.exists(f => s.suc contains f)
  
  def apply(proof: Proof[SequentProofNode]) = {
    proof foldDown { (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => node match {
      case R(left, right, pivot, _) => {
        val fixedLeft  = fixedPremises.head
        val fixedRight = fixedPremises.last
        // when both fixed premises are tautologies, fixedRight is arbitrarily preferred
        if (isTautology(fixedLeft.conclusion)) fixedRight
        else if (isTautology(fixedRight.conclusion)) fixedLeft
        else if ((left eq fixedLeft) && (right eq fixedRight)) node 
        else R(fixedLeft, fixedRight, pivot, true)
      }
      case _ => node
    }}
  }
}

