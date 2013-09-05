package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.Judgment
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}
import scala.collection.immutable.{HashMap => IMap}

//NodeInfo represents information of a node for sorting nodes in top down or bottom up pebbling algorithms
//all descriptions reference the corresponding node as n
//index i: in the original proof and in a bottom up traversal, the node was visited at the i'th iteration
//depth: number of nodes on the shortest path between the proof root and n
//numberOfChildren: the amount of children nodes of n
//lastChildOf: the amount of nodes of which n is the last child that is visited in a top down traversal
//waitForPremises: the number of currently unpebbled premises. Especially interesting when the value is set to 1, because then n can be pebbled
//usesPebbles: upper bound of pebbles that are currently used for n and its premises
//childrenNotPebbled: number of children nodes of n, that have not yet been visited. Especially interesting when the value is set to 1, because then when pebbling another child of n, the pebbles of n can be removed
class NodeInfo(val index:Int, val depth: Int, val numberOfChildren: Int, var lastChildOf:Int, var waitsForPremises: Int, var usesPebbles: Int, var childrenNotPebbled: Int){
  def incLCO = lastChildOf = lastChildOf + 1
  override def toString:String = {
    "["+index+", " + lastChildOf + ", " + numberOfChildren +"]"
  }
}

final object EmptyNI extends NodeInfo(Integer.MAX_VALUE,0,0,0,0,0,0)

abstract class AbstractPebbler extends (Proof[N] => Proof[N])  {
  
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N]
  
  def findProof(proof:Proof[N],nodeInfos: MMap[N,NodeInfo],initNodes: MSet[N]):Proof[N]
  
  var counter:Int = 0
  
  def apply(proof: Proof[N]):Proof[N] = {
    val nodeInfos:MMap[N,NodeInfo] = MMap[N,NodeInfo]()
    //Set of nodes that can be pebbled initially, i.e. the axioms
    val initNodes: MSet[N] = MSet[N]()
    counter = 0
    val proofSize= proof.size
    //traverse the proof bottom up and create a NodeInfo object for each node
    //add all nodes without premises to the set of initially pebbleable nodes
    def gather(node: N, children: Seq[N]):N = {
      if (node.premises.isEmpty) initNodes += node
      val depth = if (children.size > 0) children.map(c => nodeInfos(c).depth).min + 1 else 0
      val nI = new NodeInfo(proofSize-counter,depth,children.size, 0,node.premises.size,0,children.size)
      nodeInfos += (node -> nI)
      children.lastOption.foreach(l => nodeInfos(l).incLCO)
      counter = counter + 1
      node
    }
    proof bottomUp gather
    findProof(proof,nodeInfos,initNodes)
  }
    
}
/*****************Top down Pebblers*****************
 * Top down pebblers traverse the proof from leaves to the root and pebble nodes using a specific heuristic in form of a node ordering.
 * By pebbling nodes, other nodes are made available for pebbling and initially only nodes without premises are available.
 * This is done until no more nodes are available for pebbling, i.e. the root node is available for pebbling*/

abstract class AbstractTopDownPebbler extends AbstractPebbler  {
  def findProof(proof:Proof[N],nodeInfos: MMap[N,NodeInfo],initNodes: MSet[N]):Proof[N] = {
    //Pebbled nodes go into this Seq
    var permutation:Seq[N] = Seq[N]()
    
    val canBePebbled:MSet[N] = initNodes
//
//    //Number of premises that have not been pebbled yet
//    val waitsForPremises: MMap[N,Int] = MMap[N,Int]()
//    
//    //Number of pebbles a node uses recursively
//    val usesPebbles: MMap[N,Int] = MMap[N,Int]()
//    
//    //Number of children of a node that are currently not pebbled. Especially interesting when the number is 1, so pebbling the next child means one can remove the pebbles from this node
//    val childrenNotPebbled: MMap[N,Int] = MMap[N,Int]()
//    
    proof.nodes.foreach(n => {
      if (n.premises.isEmpty) canBePebbled += n
    })
    
    while(!canBePebbled.isEmpty) {
      //decide the next node to be pebbled by taking all pebbleable nodes and taking their maximum with the currently used Ordering
      val next = canBePebbled.max(usedOrder(proof,nodeInfos))
      
      
//      println(nodeInfos.size)
      
//      print("Available:(")
//      canBePebbled.foreach(c => print(nodeInfos(c).index +"["+new RemovesPebblesOrder(proof,nodeInfos).compute(c)  + "~"+ new DepthOrder(proof,nodeInfos).compute(c) +"~"+ new PebbledPremisesOrder(proof,nodeInfos).compute(c) + "~" + new ChildWithPebbledPremise(proof,nodeInfos).compute(c) +"] "))
//      print(")\n")
      
//      println(nodeInfos(next).index + " " + next)
//      println(next)
      permutation = permutation :+ next
      canBePebbled -= next
      next.premises.foreach(pr => {
        if (nodeInfos.isDefinedAt(pr)) {
          val cNP = nodeInfos(pr).childrenNotPebbled - 1
          //This premise can be unpebbled.
          if (cNP == 1) {
            nodeInfos -= pr
          }
          else {
            nodeInfos(pr).childrenNotPebbled = cNP
          }
        }
      })
      //calculate the number of pebbles used for this node as 1 + the sum of the usesPebbles parameters of all premises
      //Because this number if only changed when pebbling a node, it might be the case that it does not exactly represent the upper bound of used pebbles at some state,
      //but I still think it serves well enough as it is for heuristical puropses
      nodeInfos(next).usesPebbles = (1 /: next.premises) ((A,B) => A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
      
      //visit all children of the current node and decrement their waitsForPremises number by 1
      //if this number was 1 before for a children c, then c can be made available for pebbling
      proof.childrenOf(next).foreach(c => {
        val wF = nodeInfos(c).waitsForPremises
        nodeInfos(c).waitsForPremises = wF - 1
        if (wF == 1) {
          canBePebbled += c
        }
      })
      
    }
    new Proof(proof.root, permutation.reverse.toIndexedSeq)
  }
}



/*****************Bottom UP Pebblers***************** 
 * Bottom up pebblers traverse the proof from the root to the leaves.
 * At each node n its premises are visited recursively before n is processed.
 * It is decided heuristically in what order the nodes are visited.
 * So far these pebblers have behaved better in compressing the space measure than top down pebblers.
 * I think this is the case, because far new branches are not touched before old ones are finished with.
 */

abstract class AbstractBottomUpPebbler extends AbstractPebbler  {
   
  def findProof(proof:Proof[N],nodeInfos: MMap[N,NodeInfo],initNodes: MSet[N]):Proof[N] = {
    var permutation:Seq[N] = Seq[N]()
    val visited = MSet[N]()
    
    //compute the final permutation by recursively visiting the premises of nodes in the order of their NodeInfo objects, started with the root node
    //store the visited nodes, so no node is visited twice
    def visit(p:N):Unit = if (!visited(p)){
      visited += p
      var premises = p.premises
      while (!premises.isEmpty) {
        val next = premises.max(usedOrder(proof,nodeInfos))
        premises = premises.diff(Seq(next))
        visit(next)
      }
      permutation = permutation :+ p
    }
    visit(proof.root)
//    permutation.foreach(println)
    new Proof(proof.root, permutation.reverse.toIndexedSeq)
  }
}



/*****************Orderings*****************/

//Order with the number of children nodes have
class ChildrenOrder(proof: Proof[N]) extends Ordering[N] {
  def compare(a:N, b:N) = proof.childrenOf(a).size compare proof.childrenOf(b).size
}

//Order with the number of premises nodes have
class NumberOfPremisesOrder(proof: Proof[N]) extends Ordering[N] {
  def compare(a:N, b:N) = {
    a.premises.size compare b.premises.size match {
      case 0 => new ChildrenOrder(proof).compare(a, b)
      case c => c
    }
  }
}

//Order with the sizes of the subproofs of nodes, where smaller sizes are considered to give a bigger ordering
class ProofSizeOrder extends Ordering[N] {
  def compare(a:N, b:N) = {
    -(Proof(a).size compare Proof(b).size)
  }
}

//Abstract superclass for Orderings using one or more parameters from the NodeInfo objects of nodes
//Order after some computed measure, that is stored in a HashMap, so it does not have to recomputed everytime a node is compared to another
//NextOrder stands for the Ordering that should be applied in case of a draw.
abstract class UseNodeInfosOrdering(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends Ordering[N] {
  val measure = MMap[N,Int]()
  final def computeMeasure(node:N):Int = {
    val x = compute(node)
    measure(node) = x
    x
  }
  def compute(node:N):Int
  def nextOrder:Ordering[N]
  def compare(a:N, b:N) = {
    measure.getOrElse(a, computeMeasure(a)) compare measure.getOrElse(b, computeMeasure(b)) match {
      case 0 => nextOrder.compare(a, b)
      case c => c
    }
  }
}

//Order with the amount of premises that a node's children are waiting for to be pebbled
class WaitForOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node:N) = {
    (0 /: proof.childrenOf(node)) ((A,B) => A + nodeInfos.getOrElse(B,EmptyNI).waitsForPremises)
  }
  def nextOrder = new RemovesPebblesOrder(proof,nodeInfos)
}

//Order the nodes with the amount of pebbles that children nodes could remove if the current node was pebbled
//For a node n and each child c, the number pu of used pebbles of all premises of c are summed up. 
//If c is waiting for only one premise, i.e. this premise, this number is added to the measure sum for n, because if n was pebbled then c could remove pu- many pebbles in a next round.
class WaitForUsedPebblesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node:N) = {
    val x = (0 /: proof.childrenOf(node)) ((A,B) => A + (if (nodeInfos.getOrElse(B, EmptyNI).waitsForPremises == 1) premiseUP.getOrElse(B, computePUP(B)) else 0))
    measure(node) = x
    x
  }
  val premiseUP = MMap[N,Int]()
  def computePUP(node: N):Int = {
    val x = (0 /: node.premises) ((A,B) => A + (nodeInfos.getOrElse(B, EmptyNI).usesPebbles))
    premiseUP(node) = x
    x
  }
  def nextOrder = new ChildrenOrder(proof)
}

//Order with the amount of nodes that would be made available for pebbling in the next round, if a node was pebbled in the current round.
class MakesAvailableOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node:N) = {
    (0 /: proof.childrenOf(node)) ((A,B) => A + (if (nodeInfos.getOrElse(B, EmptyNI).waitsForPremises == 1) 1 else 0))
  }
  def nextOrder = new NumberOfPremisesOrder(proof)
}

//Order with the sum of pebbles that are (maximally) used for all premises of a node
class PebbledPremisesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node: N) = {
    (0 /: node.premises) ((A,B) => A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
  }
  def nextOrder = new ChildWithPebbledPremise(proof,nodeInfos)
}

//Order with the sum of pebbles that are (maximally) used for all premises, summed up over all children of a node
class ChildWithPebbledPremise(proof: Proof[N],nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node:N) = {
    (0 /: proof.childrenOf(node)) ((A,B) => A + pebbledPremises.getOrElse(B, computePP(B)))
  }
  val pebbledPremises = MMap[N,Int]()
  def computePP(node: N) = {
    val x = (0 /: node.premises) ((A,B) => A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
    pebbledPremises(node) = x
    x
  }
  def nextOrder = new IndexOrder(proof,nodeInfos)
}

//Order with the depth of a node
class DepthOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node: N) = {
    nodeInfos(node).depth
  }
  def nextOrder = new ChildrenOrder(proof)
}

//Order with the amount of pebbles this node would (maximally) remove if it was pebbled.
//If a premise is waiting for only one child to be pebbled, i.e. this node, then the amount of pebbles it uses can be removed when pebbling this node, elsewise no pebbles can be removed.
class RemovesPebblesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node: N) = {
    (0 /: node.premises) ((A,B) => A + (if (nodeInfos.getOrElse(B, EmptyNI).childrenNotPebbled == 1) 1 else 0) * nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
  }
  def nextOrder = new PebbledPremisesOrder(proof,nodeInfos)
}

//Order with the amount of nodes for which a node is the last child of.
class LastChildOfOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends Ordering[N] {
  def compare(a:N, b:N) = {
    nodeInfos(a).lastChildOf compare nodeInfos(b).lastChildOf match {
      case 0 => nodeInfos(a).numberOfChildren compare nodeInfos(b).numberOfChildren match {
        case 0 => (nodeInfos(a).index compare nodeInfos(b).index)
        case c => c
      }
      case c => c
    }
  }
}

//Order with the index of a node
class IndexOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node: N) = {
    nodeInfos(node).index
  }
  def nextOrder = new DepthOrder(proof,nodeInfos)
}

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
