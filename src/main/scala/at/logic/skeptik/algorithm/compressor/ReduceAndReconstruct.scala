package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.compressor.guard._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.Map

abstract class AbstractReduceAndReconstruct
extends CompressorAlgorithm[SequentProof] with RepeatableAlgorithm[SequentProof] {

  protected def reduce(node: SequentProof, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean)
      (fallback: (SequentProof,Boolean,Boolean) => SequentProof):SequentProof =
  node match {

    // B2
    case CutIC(CutIC(beta,gamma,s,_),alpha,t,_) if leftPremiseHasOneChild && (alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         CutIC(CutIC(beta, alpha, _ == t), gamma, _ == s)
    case CutIC(CutIC(gamma,beta,s,_),alpha,t,_) if leftPremiseHasOneChild && (alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         CutIC(gamma, CutIC(beta, alpha, _ == t), _ == s)
    case CutIC(alpha,CutIC(beta,gamma,s,_),t,_) if rightPremiseHasOneChild && (alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         CutIC(CutIC(alpha, beta, _ == t), gamma, _ == s)
    case CutIC(alpha,CutIC(gamma,beta,s,_),t,_) if rightPremiseHasOneChild && (alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         CutIC(gamma, CutIC(alpha, beta, _ == t), _ == s)

    // B3
    case CutIC(CutIC(beta,gamma,s,_),alpha,t,_) if (alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         gamma
    case CutIC(CutIC(gamma,beta,s,_),alpha,t,_) if (alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         gamma
    case CutIC(alpha,CutIC(beta,gamma,s,_),t,_) if (alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         gamma
    case CutIC(alpha,CutIC(gamma,beta,s,_),t,_) if (alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         gamma

    // B2'/B1
    case CutIC(CutIC(beta,_,s,_),alpha,t,_) if (alpha.conclusion.suc contains s) && (beta.conclusion.suc contains t) =>
         CutIC(beta, alpha, _ == t)
    case CutIC(CutIC(_,beta,s,_),alpha,t,_) if (alpha.conclusion.ant contains s) && (beta.conclusion.suc contains t) =>
         CutIC(beta, alpha, _ == t)
    case CutIC(alpha,CutIC(beta,_,s,_),t,_) if (alpha.conclusion.suc contains s) && (beta.conclusion.ant contains t) =>
         CutIC(alpha, beta, _ == t)
    case CutIC(alpha,CutIC(_,beta,s,_),t,_) if (alpha.conclusion.ant contains s) && (beta.conclusion.ant contains t) =>
         CutIC(alpha, beta, _ == t)

    // A1'
    case CutIC(CutIC(beta1,gamma1,t1,_),CutIC(beta2,gamma2,t2,_),s,_) if leftPremiseHasOneChild && rightPremiseHasOneChild &&
                                                                         (t1 == t2) && (gamma1.conclusion == beta2.conclusion) &&
                                                                         (beta1.conclusion.suc contains s) && (gamma2.conclusion.ant contains s) =>
         CutIC(CutIC(beta1,gamma2, _ == s), gamma1, _ == t1)

    case _ => fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  def a2(node: SequentProof, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = node match {
    case CutIC(CutIC(beta,gamma,s,_),alpha,t,_) if leftPremiseHasOneChild &&
                                                   !(alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         CutIC(CutIC(beta,alpha, _ == t), gamma, _ == s)
    case CutIC(CutIC(gamma,beta,s,_),alpha,t,_) if leftPremiseHasOneChild &&
                                                   !(alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         CutIC(gamma, CutIC(beta,alpha, _ == t), _ == s)
    case CutIC(alpha,CutIC(beta,gamma,s,_),t,_) if rightPremiseHasOneChild &&
                                                   !(alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         CutIC(CutIC(alpha,beta, _ == t), gamma, _ == s)
    case CutIC(alpha,CutIC(gamma,beta,s,_),t,_) if rightPremiseHasOneChild &&
                                                   !(alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         CutIC(gamma, CutIC(alpha,beta, _ == t), _ == s)

    case _ => node
  }

  protected def reconstruct(node: SequentProof, fixedLeft: SequentProof, fixedRight: SequentProof) = node match {
    case Axiom(conclusion) => Axiom(conclusion)
    case CutIC(left,right,pivot,_) => CutIC(fixedLeft, fixedRight, _ == pivot, true)
  }

  protected def reduceAndReconstruct(proof: ProofNodeCollection[SequentProof], fallback: (SequentProof,Boolean,Boolean) => SequentProof) = {
    def hasOnlyOneChild(p: SequentProof) = proof.childrenOf(p) match {
        case _::Nil => true
        case _ => false
    }
    { (node: SequentProof, fixedPremises: List[SequentProof]) => {
      val fixedNode = fixedPremises match {
        case Nil => node
        case left::right::Nil => reconstruct(node, left, right)
        case _ => throw new Exception("Wrong number of premises")
      }
      node match {
        case CutIC(left, right, _, _) => reduce(fixedNode, hasOnlyOneChild(left), hasOnlyOneChild(right))(fallback)
        case _ => fixedNode
      }
    }}
  }
}

class ReduceAndReconstruct
extends AbstractReduceAndReconstruct with RepeatableAlgorithm[SequentProof] {

  def apply(proof: ProofNodeCollection[SequentProof]) = ProofNodeCollection(proof.foldDown(reduceAndReconstruct(proof, a2)))

}

object ReduceAndReconstruct
extends ReduceAndReconstruct

class RRWithA2OnChild
extends AbstractReduceAndReconstruct {
  private def a2recursive(node: SequentProof, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = node match {
    // A2 (recursive)
    case CutIC(left,right,r,_) =>
      val nLeft  = if (leftPremiseHasOneChild)  a2(left,true,true)  else left
      val nRight = if (rightPremiseHasOneChild) a2(right,true,true) else right
      val cLeft  = nLeft  ne left
      val cRight = nRight ne right
      if (cLeft || cRight) {
        val nNode = CutIC(nLeft, nRight, _ == r)
        val reduced = reduce(nNode, cLeft || leftPremiseHasOneChild, cRight || rightPremiseHasOneChild){ (node,_,_) => node }
        if (nNode ne reduced) reduced else node
      }
      else node

    case _ => node
  }

  def apply(proof: ProofNodeCollection[SequentProof]) = ProofNodeCollection(proof.foldDown(reduceAndReconstruct(proof, a2recursive)))
}

class RRWithoutA2
extends AbstractReduceAndReconstruct {

  def apply(proof: ProofNodeCollection[SequentProof]) = ProofNodeCollection(proof.foldDown(reduceAndReconstruct(proof, { (n,_,_) => n })))

}
