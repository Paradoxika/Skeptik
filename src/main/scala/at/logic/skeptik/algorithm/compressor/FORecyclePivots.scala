package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.judgment.immutable.SetSequent

abstract class FORecyclePivots
  extends FOAbstractRPIAlgorithm with FOCollectEdgesUsingSafeLiterals with FOUnitsCollectingBeforeFixing {

  def apply(proof: Proof[SequentProofNode]) = {
    val unifiableVars = getAllVars(proof);
    val edgesToDelete = collectEdgesToDelete(proof)
    if (edgesToDelete.isEmpty) {
      proof
    } else {
      val unifiableVars = getAllVars(proof);

      Proof(proof.foldDown(fixProofNodes(edgesToDelete, unifiableVars)))
    }

  }

}

// Intersection trait is defined in FORPILU.scala

trait FOoutIntersection
  extends FOAbstractRPIAlgorithm {

  protected def computeSafeLiterals(node: SequentProofNode,
    childrensSafeLiterals: Seq[(SequentProofNode, SetSequent)],
    edgesToDelete: FOEdgesToDelete): SetSequent =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head, node, edgesToDelete)
    else
      SetSequent()

}

trait FOconclusionSequent
  extends FOAbstractRPIAlgorithm {

  protected def computeSafeLiterals(node: SequentProofNode,
    childrensSafeLiterals: Seq[(SequentProofNode, SetSequent)],
    edgesToDelete: FOEdgesToDelete): SetSequent =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head, node, edgesToDelete)
    else
      node.conclusion.toSetSequent

}

object FORecyclePivots
  extends FORecyclePivots with FOoutIntersection

object FORecyclePivotsWithIntersection
  extends FORecyclePivots with FOIntersection

object FORecyclePivotsWithConclusionSequent
  extends FORecyclePivots with FOconclusionSequent
