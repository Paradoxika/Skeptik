package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.R
import at.logic.skeptik.expression.E
import scala.collection.mutable.{HashMap => MMap}

trait AdditivityHeuristic
extends Split  {
  protected def computeAdditivities(proof: Proof[N]) = {
    var totalAdditivity = 0.toLong
    val literalAdditivity = MMap[E,Long]()
    def visit(node: N) = node match {
      case R(_,_,aux,_) =>
        val nodeAdditivity = ((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1
        totalAdditivity += nodeAdditivity
        literalAdditivity.update(aux, literalAdditivity.getOrElse(aux,0.toLong) + nodeAdditivity)
      case _ =>
    }
    proof.foreach(visit)
    (literalAdditivity, totalAdditivity)
  }

  protected def chooseVariable(literalAdditivity: collection.Map[E,Long], totalAdditivity: Long):E
  
  
  def selectVariable(proof: Proof[N]) = {
    val (literalAdditivity, totalAdditivity) = computeAdditivities(proof)
    chooseVariable(literalAdditivity, totalAdditivity)
  }
}
