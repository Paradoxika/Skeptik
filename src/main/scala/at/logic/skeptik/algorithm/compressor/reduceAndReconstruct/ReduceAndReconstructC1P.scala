package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.util.math.max
import annotation.tailrec

import baseRules._

/** Contains the rules for Reduce-and-Reconstruct
 *
 * @author Joseph Boudou
 */
object C1PRule {
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
}
import C1PRule.c1p

abstract class ReduceC1P
extends Reduce(Seq(b2b3b1,c1p))

class ReduceAndReconstructC1P(val timeout: Int)
extends ReduceC1P with TimeoutTermination


// Variants

object RRC1PSimpleTermination
extends ReduceC1P with SimpleTermination

object RRC1POverTermination
extends ReduceC1P with OverTermination

object RRC1PRandomA2
extends ReduceC1P with RandomA2
