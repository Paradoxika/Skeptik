package at.logic.skeptik

import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.Judgment
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}
import scala.util.Sorting

class Pebbler[P <: ProofNode[Judgment,P]] {

  def computePebbleNumber(proof: Proof[P]):Int = {
    computePebbleNumber(proof,(0 to proof.size -1): Seq[Int])
  }
  def computePebbleNumber(proof: Proof[P],permutation: Seq[Int]):Int = {
    val rightMostChild = MMap[P,Int]() //can only be 0,1 or 2 --> change to Byte?
    var pebbleNumber = 0
    var maxPebble = 0

    def rightMost(node: P, children: Seq[P]):P = {
      children.lastOption.foreach(n => rightMostChild(n) = rightMostChild.getOrElse(n, 0) + 1)
      node
    }
//    proof bottomUp rightMost
    proof bottomUp2(rightMost,permutation)
//    println
    def sumUp(node: P, pr: Seq[Unit]) = {
      //println("curr p# " + pebbleNumber)
      val rm = rightMostChild.getOrElse(node, 0)
      pebbleNumber += 1 - rm
      maxPebble = pebbleNumber max maxPebble
//      println(node + " new p# " + pebbleNumber + " rm: " + rm)
//      print(rm)
    }
//    println
//    println(permutation)
    proof.foldDown2(sumUp,permutation)
    maxPebble
  }
  
  def greedyPebble(proof: Proof[P]):Seq[Int] = {
    val nodeIndexChild = MSet[(P,Int,Int)]()
    var counter = 0
    var permutation:Seq[Int] = Seq()
    val visited = MSet[P]()
    
    def gather(node: P, children: Seq[P]):P = {
        val tuple = (node, counter, children.size)
        counter = counter + 1
        nodeIndexChild += tuple
        node
    }
    
    proof bottomUp gather
    
    val sortedSeq = nodeIndexChild.toSeq.sortBy(- _._3)
//    println("Sorted seq of children#")
//    sortedSeq.foreach(println)
    
    while(sortedSeq.size > visited.size) {
      val nextIndex = sortedSeq.find(T => !(visited contains T._1) && T._1.premises.forall(pr => visited contains pr))
      nextIndex.foreach(T => {
//        println()
//        print(T._1)
//        print(" " + T._2 + "\n")
        visited += T._1
        permutation = permutation :+ T._2
      })
    }
    
//    println("NM size: " + newMap.size)
//    println("iNC size: " + indexNumberChildren.size)
    permutation.reverse
  }
  
  def greedyPebble2(proof: Proof[P]):Seq[Int] = {
    val nodeInfos = MMap[P,NodeInfo]()
    var counter = 0
    var permutation:Seq[Int] = Seq()
    val visited = MSet[P]()
    
    def gather(node: P, children: Seq[P]):P = {
      val nI = new NodeInfo(node,counter,0,children.size)
      nodeInfos += (node -> nI)
      children.lastOption.foreach(l => {nodeInfos(l).incLCO})
      counter = counter + 1
      node
    }
    
    proof bottomUp gather

    def visit(p:P):Unit = if (!visited(p)){
      visited += p
      val premiseInfos = p.premises.map(nodeInfos).sorted
      premiseInfos.foreach(pI => {
        visit(pI.node)
      })
      permutation = permutation :+ nodeInfos(p).index
    }
    visit(proof.root)
    permutation.reverse
  }
    
  class NodeInfo(val node:P, val index:Int, var lastChildOf:Int, val numberOfChildren: Int) extends Ordered[NodeInfo] {
//    def compare(that: NodeInfo) = {
//      if (this.lastChildOf == that.lastChildOf) {
//          if (that.numberOfChildren == this.numberOfChildren) {
//            this.index - that.index
//          }
//          else{
//            that.numberOfChildren - this.numberOfChildren
//          }
//        }
//      else that.lastChildOf - this.lastChildOf
//    }
    def compare(that: NodeInfo) = {
      if (that.numberOfChildren == this.numberOfChildren) {    
        if (this.lastChildOf == that.lastChildOf) {
          this.index - that.index
        }
          else{
            that.lastChildOf - this.lastChildOf
          }
        }
      else that.numberOfChildren - this.numberOfChildren
    }
    def incLCO = lastChildOf = lastChildOf + 1
    override def toString:String = {
      "["+index+", " + lastChildOf + ", " + numberOfChildren +"]"
    }
  }
}