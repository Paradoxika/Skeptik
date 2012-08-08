package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}

abstract class RecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals {

  def apply(proof: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = collectEdgesToDelete(proof)
//    println(edgesToDelete.size + " edges to delete")
    if (edgesToDelete.isEmpty) proof else ProofNodeCollection(proof.foldDown(fixProofs(edgesToDelete)))
  }

}

trait outIntersection
extends AbstractRPIAlgorithm {

  protected def computeSafeLiterals(node: SequentProof,
                                    childrensSafeLiterals: List[(SequentProof, IClause)],
                                    edgesToDelete: Map[SequentProof,DeletedSide] ) : IClause =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head, node, edgesToDelete)
    else
      IClause()

}
