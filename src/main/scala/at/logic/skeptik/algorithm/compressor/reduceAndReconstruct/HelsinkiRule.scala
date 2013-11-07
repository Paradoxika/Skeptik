package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R

import baseRules._

/** The Helsinki rule is an improvement of the middleLower rule.
 *
 * @author Joseph Boudou
 */
object HelsinkiRule {
  def helsinki
      (fallback: Fun) =
      (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =>
  node match {
    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && !(o1.conclusion.suc contains u) &&
       ((o2.conclusion.ant contains u) || (o1.conclusion.width < o2.conclusion.width)) =>
         R(R(alpha,beta), o1)
    case R(R(alpha,o1,_,s),R(beta,o2,_,t),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && !(o2.conclusion.ant contains u) =>
         R(R(alpha,beta), o2)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && !(o1.conclusion.suc contains u) =>
         R(R(alpha,beta), o1)
    case R(R(o1,alpha,s,_),R(o2,beta,t,_),u,_)
    if leftPremiseHasOneChild && rightPremiseHasOneChild &&
       s == t && (alpha.conclusion.suc contains u) && (beta.conclusion.ant contains u) && !(o2.conclusion.ant contains u) =>
         R(R(alpha,beta), o2)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }
}
import HelsinkiRule.helsinki

abstract class ReduceHelsinki
extends Reduce(Seq(b2b3b1,helsinki))

class ReduceAndReconstructHelsinkiTimeout(val timeout: Int)
extends ReduceHelsinki with TimeoutTermination


// Variants

object RRHelsinkiSimpleTermination
extends ReduceHelsinki with SimpleTermination

object RRHelsinkiOverTermination
extends ReduceHelsinki with OverTermination

object RRHelsinkiRandomA2Alt
extends ReduceHelsinki with RandomA2Alt

object RRHelsinkiRandomA2
extends ReduceHelsinki with RandomA2
