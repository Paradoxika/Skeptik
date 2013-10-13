package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.util.math.max

import baseRules._


trait ReconstructWithHeight
extends Reduce
{
  // Compute the height of the original proof (not the one of the compressed proof).
  protected def reconstruct(proof: Proof[SequentProofNode], function: Fun)
                           (node: SequentProofNode, fixedPremises: Seq[(Int,SequentProofNode)]) =
    (node, fixedPremises) match {
      case (R(o_left,o_right,pivot,_), (hl,n_left)::(hr,n_right)::Nil) =>
        ((if (hl > hr) hl else hr) + 1,
         function(R(n_left, n_right, pivot, true), proof.childrenOf(o_left).length == 1, proof.childrenOf(o_right).length == 1))
      case (n, l) => (max(l, { x:(Int,SequentProofNode) => x._1}, 0) + 1, n)
    }
}
