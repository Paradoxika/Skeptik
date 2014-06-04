package at.logic.skeptik

import at.logic.skeptik.proof.sequent.lk.EqTransitive
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.util.math.max
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}
import at.logic.skeptik.proof.sequent.SequentProofNode

package object proof {
  def measure[N <: ProofNode[Judgment,N]](p: Proof[N]) = {
    var length = 0
    var transLength = 0
    var coreSize = 0
    val childrenVisited = MMap[N,Int]()
    var currentPebbles = 0 //indicates the current number of pebbles required
    var maxPebble = 0 //the maximum number of pebbles needed among all nodes, which is the pebble number
    val height =
      p foldDown { (n,heights:Seq[Int]) => 
        var step = 1
        n.premises.foreach(pr => {
          val chV = childrenVisited.getOrElse(pr, 0) + 1
          childrenVisited.update(pr, chV)
          if (chV == p.childrenOf(pr).size) {
            step = step - 1
          }
        })
        currentPebbles += step
        maxPebble = currentPebbles max maxPebble
        length += 1
        if (n.isInstanceOf[EqTransitive]) {
          transLength += (n.asInstanceOf[SequentProofNode].conclusion.ant.size - 2)*2 + 1
        }
        else transLength += 1
        if (n.premises.length == 0) coreSize += 1
        max(heights, (x:Int)=>x, default = 0) + 1
      } 
    Map("length" -> length, "coreSize" -> coreSize, "height" -> height, "space" -> maxPebble, "transLength" -> transLength)
  }
}
