package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.measure

object OrderCreator {
  def apply(orders: Seq[String], proof: Proof[N], nodeInfos: MMap[N, NodeInfo]): Ordering[N] = orders match {
    case o::rest => {
      val restOrders = OrderCreator(rest, proof, nodeInfos)
      o match {
        case "Distance1" => new DistanceOrder(proof, nodeInfos, restOrders,1)
        case "Distance2" => new DistanceOrder(proof, nodeInfos, restOrders,2)
        case "Distance3" => new DistanceOrder(proof, nodeInfos, restOrders,3)
        case "Distance4" => new DistanceOrder(proof, nodeInfos, restOrders,4)
        case "Distance5" => new DistanceOrder(proof, nodeInfos, restOrders,5)
        case "InSub" => new InSubProofOrder(proof, nodeInfos, restOrders)
        case "Children" => new ChildrenOrder(proof, restOrders)
        case "Premises" => new NumberOfPremisesOrder(proof, restOrders)
        case "ProofSize" => new ProofSizeOrder(restOrders)
        case "WaitFor" => new WaitForOrder(proof, nodeInfos, restOrders)
        case "WaitForUsed" => new WaitForUsedPebblesOrder(proof, nodeInfos, restOrders)
        case "MakesAvailable" => new MakesAvailableOrder(proof, nodeInfos, restOrders)
        case "PebbledPremises" => new PebbledPremisesOrder(proof, nodeInfos, restOrders)
        case "ChildWithPebbledPremise" => new ChildWithPebbledPremiseOrder(proof, nodeInfos, restOrders)
        case "DepthOrder" => new DepthOrder(proof, nodeInfos, restOrders)
        case "LastChild" => new LastChildOfOrder(proof, nodeInfos, restOrders)
        case "RemovesPebbles" => new RemovesPebblesOrder(proof, nodeInfos, restOrders)
        case "Index" => new IndexOrder(proof, nodeInfos, restOrders)
        case "NotBlocked" => new NotBlockedOrder(proof, nodeInfos, restOrders)
        case "SubProofPebbled" => new SubProofPebbled(proof, nodeInfos, restOrders)
        case "WasPebbled" => new WasPebbledOrder(proof, nodeInfos, restOrders)
        case _ => new DummyOrder
      }
    }
    case _ => new DummyOrder
  }
}

abstract class DecayOrder(
    proof: Proof[N], 
    nodeInfos: MMap[N,NodeInfo], 
    decay: Double, 
    premiseDepth: Int, 
    combineParents: (Seq[Double] => Double), 
    nextOrder: Ordering[N]) 
    extends Ordering[N] {
  
  def singleMeasure(node: N): Int
  
  def computeMeasure(node: N, restDepth: Int): Double = {
    if (restDepth == 0) singleMeasure(node)
    else {     
      
      val fromPremises = 
        if (node.premises.isEmpty) 0 
        else {
          val premiseMeasures = node.premises.map(pr => computeMeasure(pr, restDepth - 1))
          combineParents(premiseMeasures)*decay
        }
      fromPremises + singleMeasure(node)
    }
  }
  
  def compare(a: N, b: N) = 
    computeMeasure(a, premiseDepth) compare computeMeasure(b, premiseDepth) match {
      case 0 => nextOrder.compare(a, b)
      case c => c
    }
}


class ChildrenDecayOrder(
    proof: Proof[N], 
    nodeInfos: MMap[N,NodeInfo], 
    decay: Double,
    premiseDepth: Int,
    combineParents: (Seq[Double] => Double), 
    nextOrder: Ordering[N]) 
    extends DecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, nextOrder) {

  def singleMeasure(node: N): Int = {
    proof.childrenOf.size
  }
}

class HardSubFirstOrder(
    proof: Proof[N], 
    nodeInfos: MMap[N,NodeInfo], 
    decay: Double,
    premiseDepth: Int,
    combineParents: (Seq[Double] => Double), 
    nextOrder: Ordering[N]) 
    extends DecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, nextOrder) {

  def singleMeasure(node: N): Int = {
//    if (Proof(node).size < 1000)
//      measure(Proof(node))("space")
//    else
//      nodeInfos(node).lastChildOf
    Proof(node).size
  } 
}

class HSF extends Ordering[N] {
  val measures = MMap[N,Int]()
  
  def compare(a: N, b: N) = {
    measures.getOrElseUpdate(a, measure(Proof(a))("space")) compare measures.getOrElseUpdate(b, measure(Proof(b))("space"))
  }
}

class LastChildOfDecayOrder(
    proof: Proof[N], 
    nodeInfos: MMap[N,NodeInfo], 
    decay: Double, 
    premiseDepth: Int, 
    combineParents: (Seq[Double] => Double), 
    nextOrder: Ordering[N]) 
    extends DecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, nextOrder) {

  def singleMeasure(node: N): Int = {
    nodeInfos(node).lastChildOf
  }
}

class LastChildOfDecayOrder2(
    proof: Proof[N], 
    nodeInfos: MMap[N,NodeInfo], 
    decay: Double, 
    premiseDepth: Int, 
    combineParents: (Seq[Double] => Double), 
    nextOrder: Ordering[N]) 
    extends DecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, nextOrder) {

  def singleMeasure(node: N): Int = {
    node.premises.filter(proof.childrenOf(_).filter(nodeInfos(_).usesPebbles == 0) == 1).size
  }
}

class UsesPebblesDecayOrder(
    proof: Proof[N], 
    nodeInfos: MMap[N,NodeInfo], 
    decay: Double, 
    premiseDepth: Int, 
    combineParents: (Seq[Double] => Double), 
    nextOrder: Ordering[N]) 
    extends DecayOrder(proof, nodeInfos, decay, premiseDepth, combineParents, nextOrder) {

  def singleMeasure(node: N): Int = {
    nodeInfos(node).usesPebbles
  }
}


/*****************Orderings****************
 * Represent different heuristics for pebbling
 */

class DistanceOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N], maxDistance: Int = 3) extends Ordering[N] {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new RemovesPebblesOrder(proof,nodeInfos))
  }
  
  val spheres = MMap[N,MMap[Int,Set[N]]]()
  
  def initSpheres(node: N): MMap[Int,Set[N]] = {
    val set = proof.childrenOf(node).toSet union node.premises.toSet
    MMap[Int,Set[N]](0 -> Set[N](node), 1 -> set)
  }
  
  def calculateSphere(node: N, distance: Int): Set[N] = {
    val last = spheres(node)(distance-1)
    val border = last -- spheres(node)(distance-2)
    (border foldLeft (last)) ((A,B) => {
      A union spheres.getOrElseUpdate(B, initSpheres(B))(1)
    })
  }
  
  def closestPebble(node: N, distance: Int): (Int,Int,Int) = {
    if (distance == maxDistance + 1) (distance,0,0)
    else {
    	val spheresOfNode = spheres.getOrElseUpdate(node, initSpheres(node))
	    val distanceSphere = spheresOfNode.getOrElseUpdate(distance,calculateSphere(node,distance))
	    val usingPebbles = distanceSphere.filter(nodeInSphere => (nodeInfos.getOrElse(nodeInSphere, EmptyNI).usesPebbles) != 0)
	    if (distanceSphere.forall(nodeInSphere => (nodeInfos.getOrElse(nodeInSphere, EmptyNI).usesPebbles) == 0)) {
	      closestPebble(node,distance + 1)
	    }
	    else {
//	      println("found one: " + distance)
	      distance
	    }
    	usingPebbles.size match {
    	  case 0 => closestPebble(node,distance + 1)
    	  case c => {
    	    val lastPebbled = usingPebbles.map(n => nodeInfos(n).wasPebbled).max
    	    (distance, c, lastPebbled)
    	  }
    	}
    }
  }
  
  def compare(a: N, b: N) = {
    closestPebble(a,1)._1 compare closestPebble(b,1)._1 match { //smallest sphere with a pebbled node should win
      case 0 => closestPebble(a,1)._2 compare closestPebble(b,1)._2 match { //maximum amount of pebbled nodes in that sphere
        case 0 => closestPebble(a,1)._3 compare closestPebble(b,1)._3 match { //most recent pebbled node
          case 0 => nextOrder.compare(a, b) //compare difficulties
          case c => c
        }
        case c => c
      }
      case c => -c
    }
  }
}


class InSubProofOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) extends Ordering[N] {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new IndexOrder(proof,nodeInfos))
  }
  
  def compare(a: N, b: N) = nodeInfos(a).inSubProof compare nodeInfos(b).inSubProof match {
    case 0 => nextOrder.compare(a, b)
    case c => c
  }
}

class NotBlockedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) extends Ordering[N] {
  def compare(a: N, b: N) = 
    nodeInfos.getOrElse(a,EmptyNI).blocked compare nodeInfos.getOrElse(b,EmptyNI).blocked match {
    case 0 => nextOrder.compare(a, b)
    case c => -c
  }
}


/**
 * Order with the number of children nodes have
 */
class ChildrenOrder(proof: Proof[N], nextOrder: Ordering[N]) extends Ordering[N] {
  
  def this(proof: Proof[N]) = {
    this (proof, new DummyOrder)
  }
  
  def compare(a: N, b: N) = proof.childrenOf(a).size compare proof.childrenOf(b).size match {
    case 0 => nextOrder.compare(a, b)
    case c => c
  }
}

/**
 * Order with the number of premises nodes have
 */
class NumberOfPremisesOrder(proof: Proof[N], nextOrder: Ordering[N]) extends Ordering[N] {
  
  def this(proof: Proof[N]) = {
    this (proof, new ChildrenOrder(proof))
  }
  def compare(a: N, b: N) = a.premises.size compare b.premises.size match {
    case 0 => nextOrder.compare(a, b)
    case c => c
  }
}

/** 
 *  Order with the sizes of the subproofs of nodes, 
 *  where smaller sizes are considered to give a bigger ordering 
 */
class ProofSizeOrder(nextOrder: Ordering[N]) extends Ordering[N] {
  
  def this() = {
    this(new DummyOrder)
  }
  def compare(a: N, b: N) = (Proof(a).size compare Proof(b).size) match {
      case 0 => nextOrder.compare(a, b)
      case c => c
    }
}

/**
 * Abstract superclass for Orderings using one or more parameters from the NodeInfo objects of nodes
 * Order after some computed measure, that is stored in a HashMap, 
 * so it does not have to recomputed every time a node is compared to another
 * nextOrder stands for the Ordering that should be applied in case of a draw.
 */

abstract class UseNodeInfosOrdering(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) extends Ordering[N] {
  val measure = MMap[N,Int]()
  final def computeMeasure(node: N): Int = {
    val x = compute(node)
    measure(node) = x
    x
  }
  def compute(node:N): Int
  def compare(a: N, b: N) = {
//    if (nodeInfos(a).index == 7 && nodeInfos(b).index == 22) {
//      println(this.getClass())
//      println("7: " + measure.getOrElse(a, computeMeasure(a)))
//      println("22: " + measure.getOrElse(b, computeMeasure(b)))
//    }
    compute(a) compare compute(b) match {
      case 0 => nextOrder.compare(a, b)
      case c => c
    }
  }
}

class WasPebbledOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) 
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new RemovesPebblesOrder(proof,nodeInfos))
  }
  def compute(node: N) = {
    -nodeInfos(node).wasPebbled
  }
}

/**
 * Order with the amount of premises that a node's children are waiting for to be pebbled
 */
class WaitForOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) 
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new RemovesPebblesOrder(proof,nodeInfos))
  }
  def compute(node: N) = {
    (proof.childrenOf(node) foldLeft 0) ((A,B) => 
      A + nodeInfos.getOrElse(B,EmptyNI).waitsForPremises)
  }
}

/**
 * Order the nodes with the amount of pebbles that children nodes could remove if the current node was pebbled.
 * For a node n and each child c, the number pu of used pebbles of all premises of c are summed up. 
 * If c is waiting for only one premise, i.e. this premise, 
 * this number is added to the measure sum for n, 
 * because if n was pebbled then c could remove pu- many pebbles in a next round.
 */
class WaitForUsedPebblesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N])
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new ChildrenOrder(proof))
  }
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
}

/**
 * Order with the amount of nodes that would be made available for pebbling in the next round, 
 * if a node was pebbled in the current round.
 */
class MakesAvailableOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N])  
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new NumberOfPremisesOrder(proof))
  }
  
  def compute(node:N) = {
    (proof.childrenOf(node) foldLeft 0) ((A,B) =>
      A + (if (nodeInfos.getOrElse(B, EmptyNI).waitsForPremises == 1) 1 else 0))
  }
}

/** Order with the sum of pebbles that are (maximally) used for all premises of a node */
class PebbledPremisesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N])  
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new ChildWithPebbledPremiseOrder(proof,nodeInfos))
  }
  
  def compute(node: N) = {
    (node.premises foldLeft 0) ((A,B) => 
      A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
  }
}

/** 
 *  Order with the sum of pebbles that are (maximally) used for all premises, 
 *  summed up over all children of a node
 */
class ChildWithPebbledPremiseOrder(proof: Proof[N],nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) 
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new InSubProofOrder(proof,nodeInfos))
  }
  
  def compute(node: N) = {
    (proof.childrenOf(node) foldLeft 0) ((A,B) => 
      A + computePP(B))
  }
  val pebbledPremises = MMap[N,Int]()
  def computePP(node: N) = {
    val x = (node.premises foldLeft 0) ((A,B) => 
      A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
    pebbledPremises(node) = x
    x
  }
}

/** Order with the depth of a node */

class DepthOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) 
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new ChildrenOrder(proof))
  }
  
  def compute(node: N) = {
    nodeInfos(node).depth
  }
}

/**
 * Order with the amount of pebbles this node would (maximally) remove if it was pebbled.
 * If a premise is waiting for only one child to be pebbled, i.e. this node, 
 * then the amount of pebbles it uses can be removed when pebbling this node, 
 * otherwise no pebbles can be removed.
 */
class RemovesPebblesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) 
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new PebbledPremisesOrder(proof, nodeInfos))
  }
  
  def compute(node: N) = {
    (node.premises foldLeft 0) ((A,B) => 
      A + (if (nodeInfos.getOrElse(B, EmptyNI).childrenNotPebbled == 1)
            nodeInfos.getOrElse(B, EmptyNI).usesPebbles
          else 0)
      )
  }
}

/** Order with the amount of nodes for which a node is the last child of. */
class LastChildOfOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) extends Ordering[N] {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new ChildrenOrder(proof))
  }
  
  def compare(a: N, b: N) = {
    nodeInfos(a).lastChildOf compare nodeInfos(b).lastChildOf match {
      case 0 => nextOrder.compare(a, b)
      case c => c
    }
  }
}

class SubProofPebbled(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) 
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new LastChildOfOrder(proof, nodeInfos))
  }
  
  def compute(node: N) = {
    Proof(node).filter(n => nodeInfos(n).usesPebbles != 0).size
  }
}

/** Order with the index of a node */
class IndexOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo], nextOrder: Ordering[N]) 
  extends UseNodeInfosOrdering(proof, nodeInfos, nextOrder) {
  
  def this(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) = {
    this (proof, nodeInfos, new DepthOrder(proof,nodeInfos))
  }
  
  def compute(node: N) = {
    nodeInfos(node).index
  }
}

class DummyOrder extends Ordering[N] {
  def compare(a: N, b: N) = {
    a.hashCode() compare b.hashCode()
  }
}