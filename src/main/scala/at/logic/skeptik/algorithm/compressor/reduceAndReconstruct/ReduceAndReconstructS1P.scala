package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R

import baseRules._

/** Contains the rules for Reduce-and-Reconstruct
 *
 * @author Joseph Boudou
 */
object S1PRule {
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
}
import S1PRule.s1p

abstract class ReduceS1P
extends Reduce(Seq(b2b3b1,s1p))

class ReduceAndReconstructS1P(val timeout: Int)
extends ReduceS1P with TimeoutTermination


// Variants

object RRS1PSimpleTermination
extends ReduceS1P with SimpleTermination

object RRS1POverTermination
extends ReduceS1P with OverTermination

object RRS1PRandomA2
extends ReduceS1P with RandomA2
