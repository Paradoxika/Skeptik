package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R


/** Contains the rules for Reduce-and-Reconstruct
 *
 * @author Joseph Boudou
 */
object baseRules {
  type Fun = ((SequentProofNode,Boolean,Boolean) => SequentProofNode)
  type Rule = Fun => Fun

  def s1p
      (fallback: Fun) =
      (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =>
  node match {

    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1 eq o2) =>
         R(R(alpha,beta), o1)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1 eq o2) =>
         R(R(alpha,beta), o1)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  def c1p
      (fallback: Fun) =
      (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =>
  node match {

    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1.conclusion == o2.conclusion) =>
         R(R(alpha,beta), o1)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1.conclusion == o2.conclusion) =>
         R(R(alpha,beta), o1)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  def b2b3b1
      (fallback: Fun) =
      (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =>
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

  def a2
    (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = node match {
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
}
import baseRules._

abstract class Reduce(val rules: Seq[Rule])
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {

  def fallback
    (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =
    a2(node, leftPremiseHasOneChild, rightPremiseHasOneChild)

  protected def mergeRules(default: Fun) = (rules :\ default){ _(_) }
  lazy val reduce = mergeRules(fallback)
}
