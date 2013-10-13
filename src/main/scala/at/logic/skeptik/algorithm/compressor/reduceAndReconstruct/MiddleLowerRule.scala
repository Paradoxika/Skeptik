package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R

import baseRules._

/** Contains the rules for Reduce-and-Reconstruct
 *
 * @author Joseph Boudou
 */
object MiddleLowerRule {
  def middleLower
      (fallback: Fun) =
      (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =>
  node match {

    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1.conclusion subsequentOf o2.conclusion) =>
         R(R(alpha,beta), o1)
    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o2.conclusion subsequentOf o1.conclusion) =>
         R(R(alpha,beta), o2)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o1.conclusion subsequentOf o2.conclusion) =>
         R(R(alpha,beta), o1)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && (o2.conclusion subsequentOf o1.conclusion) =>
         R(R(alpha,beta), o2)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }
}
import MiddleLowerRule.middleLower

abstract class ReduceMiddleLower
extends Reduce(Seq(b2b3b1,middleLower))

class ReduceAndReconstructMiddleLowerTimeout(val timeout: Int)
extends ReduceMiddleLower with TimeoutTermination


// Variants

object RRMiddleLowerSimpleTermination
extends ReduceMiddleLower with SimpleTermination

object RRMiddleLowerOverTermination
extends ReduceMiddleLower with OverTermination

object RRMiddleLowerRandomA2
extends ReduceMiddleLower with RandomA2
