package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.Map

abstract class AbstractReduceAndReconstruct
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {

  protected def reduce(node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean)
      (fallback: (SequentProofNode,Boolean,Boolean) => SequentProofNode):SequentProofNode =
  node match {

    // B2
    case R(R(beta,gamma,s,_),alpha,t,_) if leftPremiseHasOneChild && (alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         R(R(beta, alpha, _ == t), gamma, _ == s)
    case R(R(gamma,beta,s,_),alpha,t,_) if leftPremiseHasOneChild && (alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         R(gamma, R(beta, alpha, _ == t), _ == s)
    case R(alpha,R(beta,gamma,s,_),t,_) if rightPremiseHasOneChild && (alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         R(R(alpha, beta, _ == t), gamma, _ == s)
    case R(alpha,R(gamma,beta,s,_),t,_) if rightPremiseHasOneChild && (alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         R(gamma, R(alpha, beta, _ == t), _ == s)

    // B3
    case R(R(beta,gamma,s,_),alpha,t,_) if (alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         gamma
    case R(R(gamma,beta,s,_),alpha,t,_) if (alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         gamma
    case R(alpha,R(beta,gamma,s,_),t,_) if (alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         gamma
    case R(alpha,R(gamma,beta,s,_),t,_) if (alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         gamma

    // B2'/B1
    case R(R(beta,_,s,_),alpha,t,_) if (alpha.conclusion.suc contains s) && (beta.conclusion.suc contains t) =>
         R(beta, alpha, _ == t)
    case R(R(_,beta,s,_),alpha,t,_) if (alpha.conclusion.ant contains s) && (beta.conclusion.suc contains t) =>
         R(beta, alpha, _ == t)
    case R(alpha,R(beta,_,s,_),t,_) if (alpha.conclusion.suc contains s) && (beta.conclusion.ant contains t) =>
         R(alpha, beta, _ == t)
    case R(alpha,R(_,beta,s,_),t,_) if (alpha.conclusion.ant contains s) && (beta.conclusion.ant contains t) =>
         R(alpha, beta, _ == t)

    // A1'
    case R(R(beta1,gamma1,t1,_),R(beta2,gamma2,t2,_),s,_) if leftPremiseHasOneChild && rightPremiseHasOneChild &&
                                                                         (t1 == t2) && (gamma1.conclusion == beta2.conclusion) &&
                                                                         (beta1.conclusion.suc contains s) && (gamma2.conclusion.ant contains s) =>
         R(R(beta1,gamma2, _ == s), gamma1, _ == t1)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  def a2(node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = node match {
    case R(R(beta,gamma,s,_),alpha,t,_) if leftPremiseHasOneChild &&
                                                   !(alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         R(R(beta,alpha, _ == t), gamma, _ == s)
    case R(R(gamma,beta,s,_),alpha,t,_) if leftPremiseHasOneChild &&
                                                   !(alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         R(gamma, R(beta,alpha, _ == t), _ == s)
    case R(alpha,R(beta,gamma,s,_),t,_) if rightPremiseHasOneChild &&
                                                   !(alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         R(R(alpha,beta, _ == t), gamma, _ == s)
    case R(alpha,R(gamma,beta,s,_),t,_) if rightPremiseHasOneChild &&
                                                   !(alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         R(gamma, R(alpha,beta, _ == t), _ == s)

    case _ => node
  }


  
  protected def reconstruct(proof: Proof[SequentProofNode], fallback: (SequentProofNode,Boolean,Boolean) => SequentProofNode)
                           (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {

    val fixedNode = (node, fixedPremises) match {
      case (R(_,_,pivot,_), left::right::Nil) => R(left, right, _ == pivot, true)
      case _ => node
    }
    node match {
      case R(left, right, _, _) => reduce(fixedNode, proof.childrenOf(left).length == 1, proof.childrenOf(right).length == 1)(fallback)
      case _ => fixedNode
    }
  }
}

class ReduceAndReconstruct(val timeout: Int)
extends AbstractReduceAndReconstruct with Timeout {
  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, a2))
}


class RRWithoutA2(val timeout: Int)
extends AbstractReduceAndReconstruct with Timeout {
  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, { (n,_,_) => n }))
}
