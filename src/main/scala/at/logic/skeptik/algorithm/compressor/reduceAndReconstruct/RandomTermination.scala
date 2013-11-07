package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import annotation.tailrec


/** Apply the fallback rule randomly.
 * The probability the fallback rule is applied is given by the member variable fallbackThreshold.
 * When the fallback rule is not applied, the node is left as is.
 */
trait RandomFallback
extends Reduce {
  private val rand = new scala.util.Random()

  protected var fallbackThreshold : Double

  abstract override def fallback
    (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) =
    if ((fallbackThreshold >= 1.0) || (rand.nextDouble() <= fallbackThreshold))
      super.fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
    else
      node
}

/** Apply A2 rule randomly with increasing probability.
 * Let c be the number of previous successive calls for which no other rule than A2 have been applied.
 * This number is equal to zero when the last call applied any other rule than A2.
 * The probability A2 is applied during the next call corresponds to this number c divided by the height of the proof.
 * The algorithm terminates when c exceeds the double of the height of the proof.
 */
trait RandomA2
extends Reduce with RandomFallback with CheckFallback {
  var fallbackThreshold = 0.0

  def apply(proof: Proof[SequentProofNode]) = {
    @tailrec
    def aux(before: Proof[SequentProofNode], count: Int): Proof[SequentProofNode] = {
      val (height, root) = applyOnce(before)
      val after = Proof(root)
      fallbackThreshold = count.toDouble / height.toDouble

      if (checkFallback > 0)
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

trait RandomA2Alt
extends Reduce with RandomFallback with CheckFallback {
  var fallbackThreshold = 0.0

  def apply(proof: Proof[SequentProofNode]) = {
    @tailrec
    def aux(before: Proof[SequentProofNode], count: Int): Proof[SequentProofNode] = {
      val (height, root) = applyOnce(before)
      val after = Proof(root)

      if (checkFallback > 0) {
        fallbackThreshold = 0.0
        aux(after, 1)
      }
      else // only A2 rule has been applied
        if (count <= height)
          aux(after, count+1)
        else
          if (fallbackThreshold < 1.0) {
            fallbackThreshold += 0.5
            aux(after, 1)
          }
          else
            after
    }
    fallbackThreshold = 0.0
    aux(proof,1)
  }
}
