package skeptik.algorithm.compressor

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.judgment.immutable.{SetSequent => IClause}
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.Map

// TODO: share code
class ReduceAndReconstruct
extends Function1[SequentProof,SequentProof] {

  def reduce(node: SequentProof, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean):SequentProof = node match {
    case Axiom(_) => node

    // B2
    case CutIC(CutIC(beta,gamma,s,_),alpha,t,_) if (alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         CutIC(CutIC(beta, alpha, _ == t), gamma, _ == s)
    case CutIC(CutIC(gamma,beta,s,_),alpha,t,_) if (alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         CutIC(gamma, CutIC(beta, alpha, _ == t), _ == s)
    case CutIC(alpha,CutIC(beta,gamma,s,_),t,_) if (alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         CutIC(CutIC(alpha, beta, _ == t), gamma, _ == s)
    case CutIC(alpha,CutIC(gamma,beta,s,_),t,_) if (alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
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

    // A2 (recursive)
    case CutIC(left,right,r,_) =>
      val nLeft  = if (leftPremiseHasOneChild)  a2(left)  else left
      val nRight = if (rightPremiseHasOneChild) a2(right) else right
      if ((nLeft ne left) || (nRight ne right)) {
        val nNode = CutIC(nLeft, nRight, _ == r)
        val reduced = reduce(nNode, false, false)
        if (nNode ne reduced) reduced else node
      }
      else node

    case _ => node
  }

  def a2(proof: SequentProof) = proof match {
    case CutIC(CutIC(beta,gamma,s,_),alpha,t,_) if !(alpha.conclusion.suc contains s) && !(gamma.conclusion.suc contains t) =>
         CutIC(CutIC(beta,alpha, _ == t), gamma, _ == s)
    case CutIC(CutIC(gamma,beta,s,_),alpha,t,_) if !(alpha.conclusion.ant contains s) && !(gamma.conclusion.suc contains t) =>
         CutIC(gamma, CutIC(beta,alpha, _ == t), _ == s)
    case CutIC(alpha,CutIC(beta,gamma,s,_),t,_) if !(alpha.conclusion.suc contains s) && !(gamma.conclusion.ant contains t) =>
         CutIC(CutIC(alpha,beta, _ == t), gamma, _ == s)
    case CutIC(alpha,CutIC(gamma,beta,s,_),t,_) if !(alpha.conclusion.ant contains s) && !(gamma.conclusion.ant contains t) =>
         CutIC(gamma, CutIC(alpha,beta, _ == t), _ == s)
    case _ => proof
  }

  def reconstruct(node: SequentProof, fixedLeft: SequentProof, fixedRight: SequentProof) = node match {
    case Axiom(conclusion) => Axiom(conclusion)
    case CutIC(left,right,aux,_) => ((fixedLeft.conclusion.suc  contains aux),
                                     (fixedRight.conclusion.ant contains aux)) match {
      case (true,true) => CutIC(fixedLeft, fixedRight, _ == aux)
      case (true,false) => fixedRight
      case (false,true) => fixedLeft
      case (false,false) => fixedLeft
    }
  }

  def apply(proof: SequentProof) = {
    val nodeCollection = ProofNodeCollection(proof)
    def hasOnlyOneChild(p: SequentProof) = nodeCollection.childrenOf(p) match {
        case _::Nil => true
        case _ => false
    }
    def visit(node: SequentProof, fixedPremises: List[SequentProof]) = {
      val fixedNode = fixedPremises match {
        case Nil => node
        case left::right::Nil => reconstruct(node, left, right)
        case _ => throw new Exception("Wrong number of premises")
      }
      node match {
        case CutIC(left, right, _, _) => reduce(fixedNode, hasOnlyOneChild(left), hasOnlyOneChild(right))
        case _ => fixedNode
      }
    }
    nodeCollection.foldDown(visit)
  }
}

