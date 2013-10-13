package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import annotation.tailrec


trait RandomFallback
extends Reduce {
  val rand = new scala.util.Random()
  var fallbackThreshold : Double
  abstract override def fallback
    (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =
    if (rand.nextDouble() <= fallbackThreshold)
      super.fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
    else
      node
}

trait RandomA2
extends Reduce with RandomFallback with CheckFallback {
  var fallbackThreshold = 0.0

  def apply(proof: Proof[SequentProofNode]) = {
    @tailrec
    def aux(before: Proof[SequentProofNode], count: Int): Proof[SequentProofNode] = {
      val (height, root) = applyOnce(before)
      val after = Proof(root)
      fallbackThreshold = count.toDouble / height.toDouble

      if (check > 0)
        aux(after, 1)
      else // only A2 rule has been applied
        if (count <= 2 * height)
          aux(after, count+1)
        else
          after
    }
    aux(proof,1)
  }
}
