package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.Judgment
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}
import scala.collection.immutable.{HashMap => IMap}

//NodeInfo represents important information for sorting the premises of nodes, these are:
//node n: n is the node to which the information belongs
//index i: in the original proof and in a bottom up traversal, the node was visited at the i'th iteration
//lastChildOf lC: the amount of nodes of which the node n is the last child that has to be visited
//numberOfChildren nC: the amount of children nodes of n
class NodeInfo(val index:Int, val depth: Int, val numberOfChildren: Int, var lastChildOf:Int, var waitsForPremises: Int, var usesPebbles: Int, var childrenNotPebbled: Int){
  def incLCO = lastChildOf = lastChildOf + 1
  override def toString:String = {
    "["+index+", " + lastChildOf + ", " + numberOfChildren +"]"
  }
}

final object EmptyNI extends NodeInfo(0,0,0,0,0,0,0)

abstract class AbstractPebbler extends (Proof[N] => Proof[N])  {
  
  def usedOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]): Ordering[N]
  
  def findProof(proof:Proof[N],nodeInfos: MMap[N,NodeInfo],initNodes: MSet[N]):Proof[N]
  
  var counter:Int = 0
  
  
  
  
  def apply(proof: Proof[N]):Proof[N] = {
    val nodeInfos:MMap[N,NodeInfo] = MMap[N,NodeInfo]()
    //Set of nodes that can be pebbled at a current state at a top down traversal
    val initNodes: MSet[N] = MSet[N]()
    counter = 0
    val proofSize= proof.size
    //traverse the proof bottom up and create a NodeInfo object for each node
    //increase the lastChildOf value of the NodeInfo object of the current nodes last child
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
/*****************Top down Pebblers*****************/
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
//      println(nodeInfos.size)
      
      print("Available:(")
      canBePebbled.foreach(c => print(nodeInfos(c).index +"["+new RemovesPebblesOrder(proof,nodeInfos).compute(c)  + "~"+ new DepthOrder(proof,nodeInfos).compute(c) +"~"+ new PebbledPremisesOrder(proof,nodeInfos).compute(c) + "~" + new ChildWithPebbledPremise(proof,nodeInfos).compute(c) +"] "))
      print(")\n")
      val next = canBePebbled.max(usedOrder(proof,nodeInfos))
      println(nodeInfos(next).index + " " + next)
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
      nodeInfos(next).usesPebbles = (1 /: next.premises) ((A,B) => A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
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

/*****************Bottom UP Pebblers*****************/
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

/*****************Orderings*****************/

class ChildrenOrder(proof: Proof[N]) extends Ordering[N] {
  def compare(a:N, b:N) = proof.childrenOf(a).size compare proof.childrenOf(b).size
}

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

class WaitForOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node:N) = {
    (0 /: proof.childrenOf(node)) ((A,B) => A + nodeInfos.getOrElse(B,EmptyNI).waitsForPremises)
  }
  def nextOrder = new RemovesPebblesOrder(proof,nodeInfos)
}

class MakesAvailableOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node:N) = {
    (0 /: proof.childrenOf(node)) ((A,B) => A + (if (nodeInfos.getOrElse(B, EmptyNI).waitsForPremises == 1) 1 else 0))
  }
  def nextOrder = new NumberOfPremisesOrder(proof)
}

class NumberOfPremisesOrder(proof: Proof[N]) extends Ordering[N] {
  def compare(a:N, b:N) = {
    a.premises.size compare b.premises.size match {
      case 0 => new ChildrenOrder(proof).compare(a, b)
      case c => c
    }
  }
}

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
  def nextOrder = new DepthOrder(proof,nodeInfos)
}

class PebbledPremisesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node: N) = {
    (0 /: node.premises) ((A,B) => A + nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
  }
  def nextOrder = new ChildWithPebbledPremise(proof,nodeInfos)
}

class DepthOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node: N) = {
    nodeInfos(node).depth
  }
  def nextOrder = new ChildrenOrder(proof)
}

class RemovesPebblesOrder(proof: Proof[N], nodeInfos: MMap[N,NodeInfo]) extends UseNodeInfosOrdering(proof,nodeInfos) {
  def compute(node: N) = {
    (0 /: node.premises) ((A,B) => A + (if (nodeInfos.getOrElse(B, EmptyNI).childrenNotPebbled == 1) 1 else 0) * nodeInfos.getOrElse(B, EmptyNI).usesPebbles)
  }
  def nextOrder = new PebbledPremisesOrder(proof,nodeInfos)
}

class ProofSizeOrder extends Ordering[N] {
  def compare(a:N, b:N) = {
    -(Proof(a).size compare Proof(b).size)
  }
}

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
