package at.logic.skeptik

import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.util.math.max
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}

package object proof {
  def measure[N <: ProofNode[Judgment,N]](p: Proof[N]) = {
    var length = 0
    var coreSize = 0
    val height =
      p foldDown { (n,heights:Seq[Int]) => 
        length += 1
        if (n.premises.length == 0) coreSize += 1
        max(heights, (x:Int)=>x, default = 0) + 1
      } 
    
    val pebble = {
      val lastChildOf = MMap[N,MSet[N]]() //key node is the last child of all nodes in the corresponding value set
      var pebbleNumber = 0 //indicates the current number of pebbles required
      var maxPebble = 0 //the maximum number of pebbles needed among all nodes, which is the pebble number
  
      //traverse the proof bottom up and update the lastChildOf entries by adding the current node to its last child
      def lastChild(node: N, children: Seq[N]):N = {
        children.lastOption.foreach(n => lastChildOf(n) = lastChildOf.getOrElse(n, MSet[N]()) += node)
        node
      }
      
      p bottomUp lastChild
      
      //compute the pebble number of the root node
  //    println
      def sumUp(node: N, pr: Seq[Unit]) = {
        //for each node the pebble number increses by 1 minus the amount of premises the current node is the last child of
        val rm = lastChildOf.getOrElse(node, MSet[N]()).size
        pebbleNumber += 1 - rm
        maxPebble = pebbleNumber max maxPebble
  //      print(rm)
      }
  //    println
  //    println(permutation)
      p foldDown sumUp
      maxPebble
    }
    Map("length" -> length, "coreSize" -> coreSize, "height" -> height, "pebble" -> pebble)
  }
}
