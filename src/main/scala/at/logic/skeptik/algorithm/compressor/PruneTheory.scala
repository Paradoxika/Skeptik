package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{Axiom, R, TheoryLemma, TheoryR}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}

/**
 * PruneTheory prunes all theory subproofs away. 
 * The lowest theory resolution inferences (i.e. TheoryR nodes)
 * are replaced by unchecked TheoryLemma leaf nodes.
 */
object PruneTheory
extends (Proof[Node] => Proof[Node]) {
  def isTheoryLemma(n: Node) = n.isInstanceOf[TheoryLemma]
  
  def apply(proof: Proof[Node]) = {
    proof foldDown { (node: Node, fixedPremises: Seq[Node]) => node match {
      case node: TheoryR => TheoryLemma(node.conclusion)
      case R(left, right, pivot, _) => {
        val fixedLeft  = fixedPremises.head
        val fixedRight = fixedPremises.last

        if ((left eq fixedLeft) && (right eq fixedRight)) node 
        else R(fixedLeft, fixedRight, pivot, true)
      }
      case _ => node
    }}
  }
}

