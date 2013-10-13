package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import annotation.tailrec


trait SimpleTermination
extends Reduce with ReconstructWithHeight {

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
