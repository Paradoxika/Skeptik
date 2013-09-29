package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}

/*****************Orderings****************
 * Represent different heuristics for pebbling
 */

/**
 * Order with the number of children nodes have
 */
class ChildrenOrder(proof: Proof[N]) extends Ordering[N] {
  def compare(a: N, b: N) = proof.childrenOf(a).size compare proof.childrenOf(b).size
}

/**
 * Order with the number of premises nodes have
 */
class NumberOfPremisesOrder(proof: Proof[N]) extends Ordering[N] {
  def compare(a: N, b: N) = {
    a.premises.size compare b.premises.size match {
      case 0 => new ChildrenOrder(proof).compare(a, b)
      case c => c
    }
  }
}

/** 
 *  Order with the sizes of the subproofs of nodes, 
 *  where smaller sizes are considered to give a bigger ordering 
 */
class ProofSizeOrder extends Ordering[N] {
  def compare(a: N, b: N) = {
    -(Proof(a).size compare Proof(b).size)
  }
}

/**
 * Abstract superclass for Orderings using one or more parameters from the NodeInfo objects of nodes
 * Order after some computed measure, that is stored in a HashMap, 
 * so it does not have to recomputed every time a node is compared to another
 * nextOrder stands for the Ordering that should be applied in case of a draw.
 */

abstract class UseNodeInfosOrdering(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends Ordering[N] {
  val measure = MMap[N,Int]()
  final def computeMeasure(node: N): Int = {
    val x = compute(node)
    measure(node) = x
    x
  }
  def compute(node:N): Int
  def nextOrder: Ordering[N]
  def compare(a: N, b: N) = 
    measure.getOrElse(a, computeMeasure(a)) compare measure.getOrElse(b, computeMeasure(b)) match {
      case 0 => nextOrder.compare(a, b)
      case c => c
    }
}

/**
 * Order with the amount of premises that a node's children are waiting for to be pebbled
 */
class WaitForOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) 
  extends UseNodeInfosOrdering(proof, nodeInfos) {
  def compute(node: N) = {
    (proof.childrenOf(node) foldLeft 0) ((A,B) => 
      A + nodeInfos.getOrElse(B,EmptyNI).waitsForPremises)
  }
  def nextOrder = new RemovesPebblesOrder(proof,nodeInfos)
}

/**
 * Order the nodes with the amount of pebbles that children nodes could remove if the current node was pebbled.
 * For a node n and each child c, the number pu of used pebbles of all premises of c are summed up. 
 * If c is waiting for only one premise, i.e. this premise, 
 * this number is added to the measure sum for n, 
 * because if n was pebbled then c could remove pu- many pebbles in a next round.
 */
class WaitForUsedPebblesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) 
  extends UseNodeInfosOrdering(proof, nodeInfos) {
  
  def compute(node: N) = {
    val x = (proof.childrenOf(node) foldLeft 0) ((A,B) => {
      A + (if (nodeInfos.getOrElse(B, EmptyNI).waitsForPremises == 1) 
            premiseUP.getOrElse(B, computePUP(B)) 
          else 0)
      })
    measure(node) = x
    x
  }
  val premiseUP = MMap[N,Int]()
  def computePUP(node: N):Int = {
    val x = (node.premises foldLeft 0) ((A,B) =>
      A + (nodeInfos.getOrElse(B, EmptyNI).usesPebbles))
    premiseUP(node) = x
    x
  }
  def nextOrder = new ChildrenOrder(proof)
}

/**
 * Order with the amount of nodes that would be made available for pebbling in the next round, 
 * if a node was pebbled in the current round.
 */
class MakesAvailableOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) 
  extends UseNodeInfosOrdering(proof, nodeInfos) {
  
  def compute(node:N) = {
    (proof.childrenOf(node) foldLeft 0) ((A,B) =>
      A + (if (nodeInfos.getOrElse(B, EmptyNI).waitsForPremises == 1) 1 else 0))
  }
  def nextOrder = new NumberOfPremisesOrder(proof)
}

/** Order with the sum of pebbles that are (maximally) used for all premises of a node */
class PebbledPremisesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) 
  extends UseNodeInfosOrdering(proof, nodeInfos) {
  
  def compute(node: N) = {
    (node.premises foldLeft 0) ((A,B) => 
      A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
  }
  def nextOrder = new ChildWithPebbledPremise(proof,nodeInfos)
}

/** 
 *  Order with the sum of pebbles that are (maximally) used for all premises, 
 *  summed up over all children of a node
 */
class ChildWithPebbledPremise(proof: Proof[N],nodeInfos: MMap[N,NodeInfo]) 
  extends UseNodeInfosOrdering(proof, nodeInfos) {
  
  def compute(node: N) = {
    (proof.childrenOf(node) foldLeft 0) ((A,B) => 
      A + pebbledPremises.getOrElse(B, computePP(B)))
  }
  val pebbledPremises = MMap[N,Int]()
  def computePP(node: N) = {
    val x = (node.premises foldLeft 0) ((A,B) => 
      A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
    pebbledPremises(node) = x
    x
  }
  def nextOrder = new IndexOrder(proof,nodeInfos)
}

/** Order with the depth of a node */

class DepthOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) 
  extends UseNodeInfosOrdering(proof, nodeInfos) {
  
  def compute(node: N) = {
    nodeInfos(node).depth
  }
  def nextOrder = new ChildrenOrder(proof)
}

/**
 * Order with the amount of pebbles this node would (maximally) remove if it was pebbled.
 * If a premise is waiting for only one child to be pebbled, i.e. this node, 
 * then the amount of pebbles it uses can be removed when pebbling this node, 
 * otherwise no pebbles can be removed.
 */
class RemovesPebblesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) 
  extends UseNodeInfosOrdering(proof, nodeInfos) {
  
  def compute(node: N) = {
    (node.premises foldLeft 0) ((A,B) => 
      A + (if (nodeInfos.getOrElse(B, EmptyNI).childrenNotPebbled == 1)
            nodeInfos.getOrElse(B, EmptyNI).usesPebbles
          else 0)
      )
  }
  def nextOrder = new PebbledPremisesOrder(proof, nodeInfos)
}

/** Order with the amount of nodes for which a node is the last child of. */
class LastChildOfOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends Ordering[N] {
  def compare(a: N, b: N) = {
    nodeInfos(a).lastChildOf compare nodeInfos(b).lastChildOf match {
      case 0 => nodeInfos(a).numberOfChildren compare nodeInfos(b).numberOfChildren match {
        case 0 => (nodeInfos(a).index compare nodeInfos(b).index)
        case c => c
      }
      case c => c
    }
  }
}

/** Order with the index of a node */
class IndexOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) 
  extends UseNodeInfosOrdering(proof, nodeInfos) {
  
  def compute(node: N) = {
    nodeInfos(node).index
  }
  def nextOrder = new DepthOrder(proof,nodeInfos)
}