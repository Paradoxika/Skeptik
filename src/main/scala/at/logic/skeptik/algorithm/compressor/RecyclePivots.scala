package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import collection.mutable.{HashMap => MMap}
import collection.Map

// For debug
import at.logic.skeptik.help._

abstract class RecyclePivots
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals {
  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(nodeCollection)
    println(edgesToDelete.size + " edges to delete")
//    for ((n,e) <- edgesToDelete) e match {
//      case LeftDS  => println(n.conclusion + " -> " + n.premises(0).conclusion)
//      case RightDS => println(n.conclusion + " -> " + n.premises(1).conclusion)
//    }
//    val debugSeq = edgesToDelete.toSeq
//    var debugNode:SequentProof = null
//    for ((n,_) <- debugSeq) n match {
//      case CutIC(_,_,pivot,_) => println(pivot) ; if (pivot.toString == "=e4ope2e1") debugNode = n
//      case _ =>
//    }
//    printDigraph("/tmp/UL", makeMapOfChildren(debugNode, nodeCollection))
    if (edgesToDelete.isEmpty) proof else nodeCollection.foldDown(fixProofs(edgesToDelete))
  }
}

trait outIntersection
extends AbstractRPIAlgorithm {
  protected def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, IClause)],
                          edgesToDelete: Map[SequentProof,DeletedSide]
                          ) : IClause =
    if (childrensSafeLiterals.length == 1)
      safeLiteralsFromChild(childrensSafeLiterals.head, proof, edgesToDelete)
    else
      IClause()
}
