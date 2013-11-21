package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import annotation.tailrec


/** Counts on how many nodes non-fallback rules have been applied.
 * The counter being a member of the trait, this trait is not thread safe.
 */
trait CheckFallback
extends Reduce with ReconstructWithHeight {
  var checkFallback = 0

  abstract override def fallback
    (node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = {
    checkFallback -= 1
    super.fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
  }

  def applyOnce(proof: Proof[SequentProofNode]) = {
    checkFallback = 0
    def pre(node: SequentProofNode, leftPremiseHasOneChild: Boolean, rightPremiseHasOneChild: Boolean) = {
      checkFallback += 1
      reduce(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
    }
    proof.foldDown(reconstruct(proof, pre))
  }
}

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
    if ((fallbackThreshold > 0.0) && ((fallbackThreshold >= 1.0) || (rand.nextDouble() <= fallbackThreshold)))
      super.fallback(node, leftPremiseHasOneChild, rightPremiseHasOneChild)
    else
      node
}

/** First only apply non-fallback rules. When no such rule have been applied in a run, apply fallback rule with probability one half
 * for as many runs as the height of the proof. Then apply fallback rule with probability one for as many runs as the height of the proof.
 * Whenever at least one non-fallback rule is applied, return to the first step.
 */
trait RandomTermination
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
      else // no non-fallback rule has been applied
        if (fallbackThreshold == 0.0) {
          fallbackThreshold = 0.5
          aux(after, 1)
        }
        else
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
