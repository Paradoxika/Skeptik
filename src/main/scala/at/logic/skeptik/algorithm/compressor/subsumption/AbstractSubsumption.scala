package at.logic.skeptik.algorithm.compressor.subsumption

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor.fixNodes
import at.logic.skeptik.proof.Proof

/**
 * Basic subsumption class
 * Uses the fixNodes traits defined in at.logic.skeptik.algorithm.compressor package object
 * Has abstract method for setting the traverse order
 */
abstract class AbstractSubsumption 
extends (Proof[N] => Proof[N]) with fixNodes {
  def setTraverseOrder(proof: Proof[N]): Proof[N]
}

/**
 * Trait for the default order of the proof
 * At the moment, the default order is left premise -> right premise -> node
 */
trait LeftRight {
  def setTraverseOrder(proof: Proof[N]):Proof[N] = proof
}

/**
 * Trait for a right premise -> left premise -> node order
 * 
 * The setTraverseOrder method reconstructs the proof using this order.
 * This needs one traversal of the whole proof.
 * Possibly a soft version of using another order would be preferable to reconstructing the proof.
 */
trait RightLeft {
  def setTraverseOrder(proof: Proof[N]):Proof[N] = new Proof(proof.root,false)
}