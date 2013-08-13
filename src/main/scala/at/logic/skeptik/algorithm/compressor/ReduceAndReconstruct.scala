package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.util.math.max
import annotation.tailrec


/** Contains the rules for Reduce-and-Reconstruct
 *
 * @author Joseph Boudou
 */
object r {
  type Fun = ((SequentProofNode,Boolean,Boolean) => SequentProofNode)
  type Rule = Fun => Fun

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


  def lowerMiddle
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
import r._

abstract class AbstractReduceAndReconstruct(val rules: Seq[Rule])
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) {

  def fallback
    (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =
    a2(node, leftPremiseHasOneChild, rightPremiseHasOneChild)

  protected def mergeRules(default: Fun) = (rules :\ default){ _(_) }
  lazy val reduce = mergeRules(fallback)
}

abstract class ReduceAndReconstruct
extends AbstractReduceAndReconstruct(Seq(b2b3b1,s1p))

abstract class ReduceAndReconstructC1P
extends AbstractReduceAndReconstruct(Seq(b2b3b1,c1p))

abstract class ReduceAndReconstructLowerMiddle
extends AbstractReduceAndReconstruct(Seq(b2b3b1,lowerMiddle))

abstract class ReduceAndReconstructHelsinki
extends AbstractReduceAndReconstruct(Seq(b2b3b1,helsinki))



trait Reconstruct
extends AbstractReduceAndReconstruct
{
  protected def reconstruct(proof: Proof[SequentProofNode], function: Fun)
                           (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) =
    (node, fixedPremises) match {
      case (R(o_left,o_right,pivot,_), n_left::n_right::Nil) =>
        function(R(n_left, n_right, pivot, true), proof.childrenOf(o_left).length == 1, proof.childrenOf(o_right).length == 1)
      case _ => node
    }
}

trait RRTimeout
extends Reconstruct with Timeout {
  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, reduce))
}

class ReduceAndReconstructTimeout(val timeout: Int)
extends ReduceAndReconstruct with RRTimeout

class RRWithLowerMiddleTimeout(val timeout: Int)
extends ReduceAndReconstructLowerMiddle with RRTimeout



trait ReconstructWithHeight
extends AbstractReduceAndReconstruct
{
  // Compute the height of the original proof (not the one of the compressed proof).
  protected def reconstruct(proof: Proof[SequentProofNode], function: Fun)
                           (node: SequentProofNode, fixedPremises: Seq[(Int,SequentProofNode)]) =
    (node, fixedPremises) match {
      case (R(o_left,o_right,pivot,_), (hl,n_left)::(hr,n_right)::Nil) =>
        ((if (hl > hr) hl else hr) + 1,
         function(R(n_left, n_right, pivot, true), proof.childrenOf(o_left).length == 1, proof.childrenOf(o_right).length == 1))
      case (n, l) => (max(l, { x:(Int,SequentProofNode) => x._1}, 0) + 1, n)
    }
}

trait SimpleTermination
extends AbstractReduceAndReconstruct with ReconstructWithHeight {

  def applyOnce(proof: Proof[SequentProofNode]) = proof.foldDown(reconstruct(proof, reduce))

  def apply(proof: Proof[SequentProofNode]) = {
    @tailrec
    def aux(before: Proof[SequentProofNode], count: Int): Proof[SequentProofNode] = {
      val (height, root) = applyOnce(before)
      val after = Proof(root)
      if (count <= height)
        aux(after, count+1)
      else
        after
    }
    aux(proof,1)
  }
}

object ReduceAndReconstructSimpleTermination
extends ReduceAndReconstruct with SimpleTermination

object RRC1PSimpleTermination
extends ReduceAndReconstructC1P with SimpleTermination

object RRWithLowerMiddleSimpleTermination
extends ReduceAndReconstructLowerMiddle with SimpleTermination

object RRWithHelsinkiSimpleTermination
extends ReduceAndReconstructHelsinki with SimpleTermination


trait CheckFallback
extends AbstractReduceAndReconstruct with ReconstructWithHeight {
  var check = 0

  abstract override def fallback
    (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = {
    check -= 1
    super.fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  def applyOnce(proof: Proof[SequentProofNode]) = {
    check = 0
    def pre(node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = {
      check += 1
      reduce(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
    }
    proof.foldDown(reconstruct(proof, pre))
  }
}

trait OverTermination
extends AbstractReduceAndReconstruct with CheckFallback {
  
  def apply(proof: Proof[SequentProofNode]) = {
    @tailrec
    def aux(before: Proof[SequentProofNode], count: Int): Proof[SequentProofNode] = {
      val (height, root) = applyOnce(before)
      val after = Proof(root)

      if (check > 0)
        aux(after, 1)
      else // only A2 rule has been applied
        if (count <= height)
          aux(after, count+1)
        else
          after
    }
    aux(proof,1)
  }
}

object ReduceAndReconstructOverTermination
extends ReduceAndReconstruct with OverTermination

object RRC1POverTermination
extends ReduceAndReconstructC1P with OverTermination

object RRWithLowerMiddleOverTermination
extends ReduceAndReconstructLowerMiddle with OverTermination

object RRWithHelsinkiOverTermination
extends ReduceAndReconstructHelsinki with OverTermination

object C1POverTermination
extends AbstractReduceAndReconstruct(Seq(c1p)) with OverTermination

object S1POverTermination
extends AbstractReduceAndReconstruct(Seq(s1p)) with OverTermination
