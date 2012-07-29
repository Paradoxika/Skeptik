package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.expression._

abstract class FixingAlgorithm
extends (SequentProof => SequentProof) {
  protected def heuristicChoosePremise(left: SequentProof, right: SequentProof):SequentProof

  def fixNode(pivot: E, left: SequentProof, right: SequentProof) =
    (left.conclusion.suc contains pivot, right.conclusion.ant contains pivot) match {
      case (true, true)  => CutIC(left, right, _ == pivot)
      case (true, false) => right
      case (false,true)  => left
      case (false,false) => heuristicChoosePremise(left,right)
    }
}

trait LeftHeuristic 
extends FixingAlgorithm {
  protected def heuristicChoosePremise (left: SequentProof, right: SequentProof):SequentProof = left
}

trait MinConclusionHeuristic
extends FixingAlgorithm {
  protected def heuristicChoosePremise(left: SequentProof, right: SequentProof):SequentProof = {
    def sequentSize(s: Sequent) = s.ant.length + s.suc.length
    if (sequentSize(left.conclusion) < sequentSize(right.conclusion)) left else right
  }
}

trait MinProofHeuristic
extends FixingAlgorithm {
  protected def heuristicChoosePremise(left: SequentProof, right: SequentProof):SequentProof = {
    if (ProofNodeCollection(left).size < ProofNodeCollection(right).size) left else right
  }
}
