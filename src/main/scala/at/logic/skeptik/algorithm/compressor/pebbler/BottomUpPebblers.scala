package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}

/*****************Bottom-up Pebblers****************
 * Pebblers only differ in the used order, i.e. the heuristic
 * */

object ProofSizeBUPebbler extends AbstractBottomUpPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new ProofSizeOrder
  }
}

object LastChildOfBUPebbler extends AbstractBottomUpPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new LastChildOfOrder(proof,nodeInfos)
  }
}

class GenericBUPebbler(inOrderings: Seq[String]) extends AbstractBottomUpPebbler with GenericPebbler {
  def orderings: Seq[String] = inOrderings
}

object WasPebbledPebbler extends AbstractBottomUpPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new WasPebbledOrder(proof,nodeInfos)
  }
}

class ChildrenDecayPebbler(decay: Double, premiseDepth: Int, combineParents: (Seq[Double] => Double)) 
    extends AbstractBottomUpPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new ChildrenDecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, new InSubProofOrder(proof, nodeInfos))
  }
}


class HardSubFirstPebbler(decay: Double, premiseDepth: Int, combineParents: (Seq[Double] => Double)) 
    extends AbstractBottomUpPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
//    new HardSubFirstOrder(proof, nodeInfos, decay, premiseDepth, combineParents, new InSubProofOrder(proof, nodeInfos))
    new HSF
  }
}

class LastChildOfDecayPebbler(decay: Double, premiseDepth: Int, combineParents: (Seq[Double] => Double)) 
    extends AbstractBottomUpPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new LastChildOfDecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, new InSubProofOrder(proof, nodeInfos))
  }
}

class LastChildOfDecayPebblerNew(decay: Double, premiseDepth: Int, combineParents: (Seq[Double] => Double)) 
    extends AbstractBottomUpPebbler with lastChildNew {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new LastChildOfDecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, new InSubProofOrder(proof, nodeInfos))
  }
}

class LastChildOfDecayPebbler2(decay: Double, premiseDepth: Int, combineParents: (Seq[Double] => Double)) 
    extends AbstractBottomUpPebbler {
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new LastChildOfDecayOrder2(proof, nodeInfos, decay, premiseDepth, combineParents, new InSubProofOrder(proof, nodeInfos))
  }
}

class LcoDCthenDistancePebbler(decay: Double, premiseDepth: Int, combineParents: (Seq[Double] => Double)) 
    extends AbstractBottomUpPebbler {
  override def findFirstOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new LastChildOfDecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, new InSubProofOrder(proof, nodeInfos))
  }
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new DistanceOrder(proof, nodeInfos, findFirstOrder(proof, nodeInfos), 3)
  }
}

class InSubThenUsesPebblesPebbler(decay: Double, premiseDepth: Int, combineParents: (Seq[Double] => Double)) 
    extends AbstractBottomUpPebbler {
  override def findFirstOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new LastChildOfDecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, new InSubProofOrder(proof, nodeInfos))
//    new InSubProofOrder(proof, nodeInfos)
  }
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N] = {
    new UsesPebblesDecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, findFirstOrder(proof, nodeInfos))
  }
}