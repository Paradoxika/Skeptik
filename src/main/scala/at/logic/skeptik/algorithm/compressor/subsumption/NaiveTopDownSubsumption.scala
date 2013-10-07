package at.logic.skeptik.algorithm.compressor.subsumption

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.Proof
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

/**
 * Naive top-down subsumption storing the (not subsumed) visited nodes in a map with their conclusion sequents.
 * 
 * At every node the node-map is searched for a subsuming node. 
 * (Where node1 is said to subsume node2 iff their conlcusion sequents do so)
 * If there is a subsuming node, then the current node is replaced by that one.
 * Otherwise the current node is stored in the map with its conclusion sequents. 
 */
abstract class NaiveTopDownSubsumption extends AbstractSubsumption {
  def apply(inputproof: Proof[N]) = {
    val proof = setTraverseOrder(inputproof)
    val nodeMap = new MMap[Sequent,N]
    Proof(proof foldDown { ((node: N, fixedPremises: Seq[N]) => {
        val subsumer = nodeMap.find( A => A._1.subsequentOf(node.conclusion))
        val subsMap = subsumer.map(a => a._2)
        
        subsMap.getOrElse({
          val newNode = fixNode(node,fixedPremises)
          nodeMap += (newNode.conclusion -> newNode)
          newNode
        })
      })
    })
  }
}

object NaiveTopDownSubsumption extends NaiveTopDownSubsumption with LeftRight

object NaiveTopDownSubsumptionRightLeft extends NaiveTopDownSubsumption with RightLeft