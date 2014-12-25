package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}

trait GenericPebbler {
  def orderings: Seq[String]
  var order: Option[Ordering[N]] = None
  var currentProof: Proof[N] = null
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    if (!order.isDefined || proof != currentProof) {
      currentProof = proof
      order = Some(OrderCreator(orderings, proof, nodeInfos))
    }
    order.get
  }
}