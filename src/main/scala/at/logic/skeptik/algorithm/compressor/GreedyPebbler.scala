package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.Judgment
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}
import scala.collection.immutable.{HashMap => IMap}

object GreedyPebbler extends (Proof[SequentProofNode] => Proof[SequentProofNode])  {
  def computePebbleNumber(proof: Proof[SequentProofNode]):Int = {
    computePebbleNumber(proof,(0 to proof.size -1): Seq[Int])
  }
  def computePebbleNumber(proof: Proof[SequentProofNode],permutation: Seq[Int]):Int = {
    val lastChildOf = MMap[SequentProofNode,MSet[SequentProofNode]]() //key node is the last child of all nodes in the corresponding value set
    var pebbleNumber = 0 //indicates the current number of pebbles required
    var maxPebble = 0 //the maximum number of pebbles needed among all nodes, which is the pebble number

    //traverse the proof bottom up and update the lastChildOf entries by adding the current node to its last child
    def lastChild(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      children.lastOption.foreach(n => lastChildOf(n) = lastChildOf.getOrElse(n, MSet[SequentProofNode]()) += node)
      node
    }
    
    proof bottomUp2(lastChild,permutation)
    
    //compute the pebble number of the root node
//    println
    def sumUp(node: SequentProofNode, pr: Seq[Unit]) = {
      //for each node the pebble number increses by 1 minus the amount of premises the current node is the last child of
      val rm = lastChildOf.getOrElse(node, MSet[SequentProofNode]()).size
      pebbleNumber += 1 - rm
      maxPebble = pebbleNumber max maxPebble
//      print(rm)
    }
//    println
//    println(permutation)
    proof.foldDown2(sumUp,permutation)
    maxPebble
  }
  
  def apply(proof: Proof[SequentProofNode]):Proof[SequentProofNode] = {
    val nodeInfos = MMap[SequentProofNode,NodeInfo]()
    var counter = 0
    var permutation:Seq[Int] = Seq()
    val visited = MSet[SequentProofNode]()
    val premisePermutation = MMap[SequentProofNode,MMap[SequentProofNode,SequentProofNode]]()
    
    //traverse the proof bottom up and create a NodeInfo object for each node
    //increase the lastChildOf value of the NodeInfo object of the current nodes last child
    def gather(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      val nI = new NodeInfo(node,counter,0,children.size)
      nodeInfos += (node -> nI)
      children.lastOption.foreach(l => nodeInfos(l).incLCO)
      counter = counter + 1
      node
    }
    
    proof bottomUp gather

    //compute the final permutation by recursively visiting the premises of nodes in the order of their NodeInfo objects, started with the root node
    //store the visited nodes, so no node is visited twice
    def visit(p:SequentProofNode):Unit = if (!visited(p)){
      visited += p
      val premiseInfos = p.premises.map(nodeInfos).sorted
//      premiseInfos.foreach(println)
//      println
      val premisesIndexed = p.premises.toIndexedSeq
      val premiseMap = MMap[SequentProofNode,SequentProofNode]()
      for (i <- 0 to premiseInfos.size) {
//        premiseMap += (p.premises(i) -> premiseInfos(i).node)
      }
      var i = 0
      premiseInfos.foreach(pI => {
        premiseMap += (premisesIndexed(i) -> pI.node) 
        i = i + 1
        visit(pI.node)
      })
      premisePermutation += (p -> premiseMap)
      permutation = permutation :+ nodeInfos(p).index
    }
    visit(proof.root)
    permutation.reverse
//    premisePermutation.foreach(println)
    new Proof(proof.root,premisePermutation)
  }
    
  //NodeInfo represents important information for sorting the premises of nodes, these are:
  //node n: n is the node to which the information belongs
  //index i: in the original proof and in a bottom up traversal, the node was visited at the i'th iteration
  //lastChildOf lC: the amount of nodes of which the node n is the last child that has to be visited
  //numberOfChildren nC: the amount of children nodes of n
  class NodeInfo(val node:SequentProofNode, val index:Int, var lastChildOf:Int, val numberOfChildren: Int) extends Ordered[NodeInfo] {
    //The parameters are prioritised in the following order for sorting a collection of NodeInfo objects:
    //lastChildOf > numberOfChildren > index
    def compare(that: NodeInfo): Int = {
      (this.lastChildOf compare that.lastChildOf) match {
        case 0 => {
          this.numberOfChildren compare that.numberOfChildren match {
            case 0 => -(this.index compare that.index)
            case c => -c
          }
        }
        case c => -c
      }
//      this.numberOfChildren compare that.numberOfChildren match {
//        case 0 => {
//          (this.lastChildOf compare that.lastChildOf) match {
//            case 0 => -(this.index compare that.index)
//            case c => -c
//          }
//        }
//        case c => -c
//      }
    }
    def incLCO = lastChildOf = lastChildOf + 1
    override def toString:String = {
      "["+index+", " + lastChildOf + ", " + numberOfChildren +"]"
    }
  }
}