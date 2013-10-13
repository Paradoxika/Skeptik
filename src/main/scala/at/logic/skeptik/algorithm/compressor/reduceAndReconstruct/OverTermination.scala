package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import annotation.tailrec


trait CheckFallback
extends Reduce with ReconstructWithHeight {
  var check = 0

  abstract override def fallback
    (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = {
    check -= 1
    super.fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  def applyOnce(proof: Proof[SequentProofNode]) = {
    check = 0
    def pre(node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = {
      check += 1
      reduce(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
    }
    proof.foldDown(reconstruct(proof, pre))
  }
}

trait OverTermination
extends Reduce with CheckFallback {
  
  def apply(proof: Proof[SequentProofNode]) = {
    @tailrec
    def aux(before: Proof[SequentProofNode], count: Int): Proof[SequentProofNode] = {
      val (height, root) = applyOnce(before)
      val after = Proof(root)

      if (check > 0)
        aux(after, 1)
      else // only A2 rule has been applied
        if (count <= height)
          aux(after, count+1)
        else
          after
    }
    aux(proof,1)
  }
}
