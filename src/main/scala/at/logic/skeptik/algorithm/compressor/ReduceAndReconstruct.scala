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

  protected def lowerMiddle
      (fallback: (SequentProofNode,Boolean,Boolean) => SequentProofNode)
      (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean):SequentProofNode =
  node match {

    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1.conclusion subsequentOf o2.conclusion) =>
//         print("Case 1 : ({"+alpha.conclusion+"}.{"+o1.conclusion+"}).({"+beta.conclusion+"}.{"+o2.conclusion+"}) ; "+s+", "+t+", "+u+"\n")
         R(R(alpha,beta), o1)
    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o2.conclusion subsequentOf o1.conclusion) =>
//         print("Case 2 : ({"+alpha.conclusion+"}.{"+o1.conclusion+"}).({"+beta.conclusion+"}.{"+o2.conclusion+"}) ; "+s+", "+t+", "+u+"\n")
         R(R(alpha,beta), o2)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1.conclusion subsequentOf o2.conclusion) =>
//         print("Case 3 : ({"+alpha.conclusion+"}.{"+o1.conclusion+"}).({"+beta.conclusion+"}.{"+o2.conclusion+"}) ; "+s+", "+t+", "+u+"\n")
         R(R(alpha,beta), o1)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o2.conclusion subsequentOf o1.conclusion) =>
//         print("Case 4 : ({"+alpha.conclusion+"}.{"+o1.conclusion+"}).({"+beta.conclusion+"}.{"+o2.conclusion+"}) ; "+s+", "+t+", "+u+"\n")
         R(R(alpha,beta), o2)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  protected def a1p
      (fallback: (SequentProofNode,Boolean,Boolean) => SequentProofNode)
      (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean):SequentProofNode =
  node match {

    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1.conclusion == o2.conclusion) =>
//         print("Case 1 : ({"+alpha.conclusion+"}.{"+o1.conclusion+"}).({"+beta.conclusion+"}.{"+o2.conclusion+"}) ; "+s+", "+t+", "+u+"\n")
         R(R(alpha,beta), o1)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1.conclusion == o2.conclusion) =>
//         print("Case 3 : ({"+alpha.conclusion+"}.{"+o1.conclusion+"}).({"+beta.conclusion+"}.{"+o2.conclusion+"}) ; "+s+", "+t+", "+u+"\n")
         R(R(alpha,beta), o1)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  protected def reduce
      (fallback: (SequentProofNode,Boolean,Boolean) => SequentProofNode)
      (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean):SequentProofNode =
  node match {

    // B2
    case R(R(beta,gamma,s,_),alpha,t,_) if leftPremiseHasOneChild && (alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         R(R(beta, alpha, t), gamma, s)
    case R(R(gamma,beta,s,_),alpha,t,_) if leftPremiseHasOneChild && (alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         R(gamma, R(beta, alpha, t), s)
    case R(alpha,R(beta,gamma,s,_),t,_) if rightPremiseHasOneChild && (alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         R(R(alpha, beta, t), gamma, s)
    case R(alpha,R(gamma,beta,s,_),t,_) if rightPremiseHasOneChild && (alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         R(gamma, R(alpha, beta, t), s)

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
         R(beta, alpha, t)
    case R(R(_,beta,s,_),alpha,t,_) if (alpha.conclusion.ant contains s) && (beta.conclusion.suc contains t) =>
         R(beta, alpha, t)
    case R(alpha,R(beta,_,s,_),t,_) if (alpha.conclusion.suc contains s) && (beta.conclusion.ant contains t) =>
         R(alpha, beta, t)
    case R(alpha,R(_,beta,s,_),t,_) if (alpha.conclusion.ant contains s) && (beta.conclusion.ant contains t) =>
         R(alpha, beta, t)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  def a2(node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = node match {
    case R(R(beta,gamma,s,_),alpha,t,_) if leftPremiseHasOneChild &&
                                                   !(alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         R(R(beta,alpha, t), gamma, s)
    case R(R(gamma,beta,s,_),alpha,t,_) if leftPremiseHasOneChild &&
                                                   !(alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         R(gamma, R(beta,alpha, t), s)
    case R(alpha,R(beta,gamma,s,_),t,_) if rightPremiseHasOneChild &&
                                                   !(alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         R(R(alpha,beta, t), gamma, s)
    case R(alpha,R(gamma,beta,s,_),t,_) if rightPremiseHasOneChild &&
                                                   !(alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         R(gamma, R(alpha,beta, t), s)

    case _ => node
  }


  
  protected def reconstruct(proof: Proof[SequentProofNode], function: (SequentProofNode,Boolean,Boolean) => SequentProofNode)
                           (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
    (node, fixedPremises) match {
      case (R(o_left,o_right,pivot,_), n_left::n_right::Nil) =>
        function(R(n_left, n_right, pivot, true), proof.childrenOf(o_left).length == 1, proof.childrenOf(o_right).length == 1)
      case _ => node
    }
  }
}

class ReduceAndReconstruct(val timeout: Int)
extends AbstractReduceAndReconstruct with Timeout {
  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, reduce(a1p(a2))))
}


class RRWithoutA2(val timeout: Int)
extends AbstractReduceAndReconstruct with Timeout {
  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, reduce(a1p({ (n,_,_) => n }))))
}


class RRWithLowerMiddle(val timeout: Int)
extends AbstractReduceAndReconstruct with Timeout {
  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, reduce(lowerMiddle(a2))))
}


class LowerMiddleA2(val timeout: Int)
extends AbstractReduceAndReconstruct with Timeout {
  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, a1p(a2)))
}

