package skeptik.algorithm.compressor

import skeptik.proof.sequent._
import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.Map


abstract class RecyclePivots
extends Function1[SequentProof,SequentProof] {

  protected sealed abstract  class DeletedSide
  protected object LeftDS  extends DeletedSide
  protected object RightDS extends DeletedSide

  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, Set[E], Set[E])) => (Set[E],Set[E])
                          ) : (Set[E],Set[E])

  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof

  private def collectEdgesToDelete(iterator: ProofNodeCollection[SequentProof]): Map[SequentProof,DeletedSide] = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      val (safeL,safeR) = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
      p match {
        case CutIC(_,_,auxL,_) if safeR contains auxL => edgesToDelete.update(p, RightDS)
        case CutIC(_,_,_,auxR) if safeL contains auxR => edgesToDelete.update(p, LeftDS)
        case _ => Unit
      }
      (p, safeL, safeR)
    }
    iterator.bottomUp(visit)
    edgesToDelete
  }

  private def fixProofs(edgesToDelete: Map[SequentProof,DeletedSide])
               (p: SequentProof, fixedPremises: List[SequentProof]) = {
    lazy val fixedLeft  = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => Axiom(conclusion)
      case CutIC(left,right,_,_) if edgesToDelete contains p => edgesToDelete(p) match {
        case LeftDS  => fixedRight
        case RightDS => fixedLeft
      }
      case CutIC(left,right,auxL,auxR) => ((fixedLeft.conclusion.suc  contains auxL),
                                           (fixedRight.conclusion.ant contains auxR)) match {
        case (true,true) => CutIC(fixedLeft, fixedRight, auxL, auxR)
        case (true,false) => fixedRight
        case (false,true) => fixedLeft
        case (false,false) => heuristicChoose(fixedLeft, fixedRight)
      }
    }
  }

  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(iterator)
    if (edgesToDelete.isEmpty) proof else iterator.foldDown(fixProofs(edgesToDelete))
  }
}

trait outIntersection
extends RecyclePivots {
  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, Set[E], Set[E])) => (Set[E],Set[E])
                          ) : (Set[E],Set[E]) =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head)
    else
      (Set[E](), Set[E]())
}

trait Intersection
extends RecyclePivots {
  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, Set[E], Set[E])) => (Set[E],Set[E])
                          ) : (Set[E],Set[E]) =
    childrensSafeLiterals match {
      case Nil  => (Set[E](proof.conclusion.ant:_*), Set[E](proof.conclusion.suc:_*))
      case h::t => t.foldLeft(safeLiteralsFromChild(h))((acc, v) => {
        val (safeL, safeR) = safeLiteralsFromChild(v)
        (acc._1 intersect safeL, acc._2 intersect safeR)
      })
  }
}

trait OptimizedIntersection
extends RecyclePivots {
  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, Set[E], Set[E])) => (Set[E],Set[E])
                          ) : (Set[E],Set[E]) = {
    def deletedChildIsCurrentProof(p: SequentProof) = edgesToDelete(p) match {
      case LeftDS  => proof == p.premises(0)
      case RightDS => proof == p.premises(1)
    }
    def notToBeDeletedEdgeFrom(tuple: (SequentProof, Set[E], Set[E])) =
      ! (edgesToDelete.contains(tuple._1) && deletedChildIsCurrentProof(tuple._1))
    childrensSafeLiterals.filter(notToBeDeletedEdgeFrom) match {
      case Nil  => (Set[E](proof.conclusion.ant:_*), Set[E](proof.conclusion.suc:_*))
      case h::t => t.foldLeft(safeLiteralsFromChild(h)) { (acc, v) =>
        val (safeL, safeR) = safeLiteralsFromChild(v)
        (acc._1 intersect safeL, acc._2 intersect safeR)
      }
    }
  }
}

trait LeftHeuristic
extends RecyclePivots {
  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof = left
}

trait MinConclusionHeuristic
extends RecyclePivots {
  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof = {
    def sequentSize(s: Sequent) = s.ant.length + s.suc.length
    if (sequentSize(left.conclusion) < sequentSize(right.conclusion)) left else right
  }
}

trait MinProofHeuristic
extends RecyclePivots {
  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof = {
    if (ProofNodeCollection(left).size < ProofNodeCollection(right).size) left else right
  }
}
