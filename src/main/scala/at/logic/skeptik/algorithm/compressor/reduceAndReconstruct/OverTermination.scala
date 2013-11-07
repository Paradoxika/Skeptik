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


/** Calls recursively the Reduce-and-Reconstruct algorithm checking whether non-fallback rules have been applied for each call.
 * Terminates when the number of successive calls for which only fallback rules have been applied exceeds the height of the proof.
 * This termination condition ensures that further applications of the rules would not reduce the size of the proof.
 */
trait OverTermination
extends Reduce with CheckFallback {
  
  def apply(proof: Proof[SequentProofNode]) = {
    println(" go")
    @tailrec
    def aux(before: Proof[SequentProofNode], count: Int, total: Int): Proof[SequentProofNode] = {
      val (height, root) = applyOnce(before)
      val after = Proof(root)

      if (checkFallback > 0) {
        println(total+":"+count+":"+height)
        aux(after, 1, total+1)
      }
      else // only A2 rule has been applied
        if (count - 700 <= height)
          aux(after, count+1, total+1)
        else {
          println(total+":"+count+":"+height)
          after
        }
    }
    aux(proof,1,1)
  }
}
