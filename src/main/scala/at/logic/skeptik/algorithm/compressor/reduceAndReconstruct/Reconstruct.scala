package at.logic.skeptik.algorithm.compressor.reduceAndReconstruct

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.R

import baseRules._

/** Applies rules inconditionaly to each resolution node.
 */
trait Reconstruct
extends Reduce
{
  /** Gives a function to be passed to Proof.foldDown.
   */
  protected def reconstruct(proof: Proof[SequentProofNode], function: Fun)
                           (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) =
    (node, fixedPremises) match {
      case (R(o_left,o_right,pivot,_), n_left::n_right::Nil) =>
        function(R(n_left, n_right, pivot, true), proof.childrenOf(o_left).length == 1, proof.childrenOf(o_right).length == 1)
      case _ => node
    }
}
