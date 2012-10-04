package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import collection._

abstract class RecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals {

  def apply(proof: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = EdgesToDelete()
//    println(edgesToDelete.size + " edges to delete")
    if (edgesToDelete.isEmpty) proof else ProofNodeCollection(proof.foldDown(fixProofs(edgesToDelete)))
  }

}

// Intersection trait is defined is RPILU.scala

trait outIntersection
extends AbstractRPIAlgorithm {

  protected def computeSafeLiterals(node: SequentProof,
                                    childrensSafeLiterals: List[(SequentProof, IClause)],
                                    edgesToDelete: EdgesToDelete ) : IClause =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head, node, edgesToDelete)
    else
      IClause()

}

object RecyclePivots
extends RecyclePivots with outIntersection with IdempotentAlgorithm[SequentProof]

object RecyclePivotsWithIntersection
extends RecyclePivots with Intersection with RepeatableWhileCompressingAlgorithm[SequentProof]

object IdempotentRecyclePivotsWithIntersection
extends RecyclePivots with Intersection with IdempotentAlgorithm[SequentProof]
