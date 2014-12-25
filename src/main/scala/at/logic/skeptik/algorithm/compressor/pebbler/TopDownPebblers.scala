package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}

/*****************Top-down Pebblers****************
 * Pebblers only differ in the used order, i.e. the heuristic
 * */

object NumberOfChildrenPebbler extends AbstractTopDownPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new ChildrenOrder(proof)
  }
}

object LeastWaitingForPebbler extends AbstractTopDownPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new WaitForOrder(proof,nodeInfos)
  }
}

object LwfUPPebbler extends AbstractTopDownPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new WaitForUsedPebblesOrder(proof,nodeInfos)
  }
}

object RemoveMostPebbles extends AbstractTopDownPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new RemovesPebblesOrder(proof,nodeInfos)
  }
}

object DistancePebbler extends AbstractTopDownPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new DistanceOrder(proof,nodeInfos)
  }
}

class GenericTDPebbler(inOrderings: Seq[String]) extends AbstractTopDownPebbler with GenericPebbler {
  def orderings: Seq[String] = inOrderings
}