package skeptik.algorithm.compressor

import skeptik.proof.sequent._
import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import collection.mutable.{HashMap => MMap}
import collection.Map


abstract class RecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals {
  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(iterator)
    if (edgesToDelete.isEmpty) proof else iterator.foldDown(fixProofs(edgesToDelete))
  }
}

trait outIntersection
extends AbstractRPIAlgorithm {
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

trait MinConclusionHeuristic
extends AbstractRPILUAlgorithm {
  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof = {
    def sequentSize(s: Sequent) = s.ant.length + s.suc.length
    if (sequentSize(left.conclusion) < sequentSize(right.conclusion)) left else right
  }
}

trait MinProofHeuristic
extends AbstractRPILUAlgorithm {
  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof = {
    if (ProofNodeCollection(left).size < ProofNodeCollection(right).size) left else right
  }
}
