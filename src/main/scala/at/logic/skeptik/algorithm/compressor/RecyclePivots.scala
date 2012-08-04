package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import collection.mutable.{HashMap => MMap}
import collection.Map


abstract class RecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals {
  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(nodeCollection)
    if (edgesToDelete.isEmpty) proof else nodeCollection.foldDown(fixProofs(edgesToDelete))
  }
}

trait outIntersection
extends AbstractRPIAlgorithm {
  protected def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, IClause)],
                          edgesToDelete: Map[SequentProof,DeletedSide]
                          ) : IClause =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head, proof, edgesToDelete)
    else
      IClause()
}
