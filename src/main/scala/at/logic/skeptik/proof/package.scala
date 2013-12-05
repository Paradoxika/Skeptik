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
    
    val space = {
      val childrenVisited = MMap[N,Int]()
      var currentPebbles = 0 //indicates the current number of pebbles required
      var maxPebble = 0 //the maximum number of pebbles needed among all nodes, which is the pebble number
      
//      var counter = 1
      //compute the pebble number of the root node
      def sumUp(node: N, pr: Seq[Unit]) = {
        //for each node the pebble number increses by 1 minus the amount of premises the current node is the last child of
        var step = 1
        node.premises.foreach(pr => {
          val chV = childrenVisited.getOrElse(pr, 0) + 1
          childrenVisited.update(pr, chV)
          if (chV == p.childrenOf(pr).size) {
            step = step - 1
//            println("node: " + node + " is last Child of: " + pr)
          }
        })
//        println(counter + " : " + step)
//        counter = counter + 1
        currentPebbles += step
        maxPebble = currentPebbles max maxPebble
      }
      p foldDown sumUp
      maxPebble
    }
    Map("length" -> length, "coreSize" -> coreSize, "height" -> height, "space" -> space)
  }
}
