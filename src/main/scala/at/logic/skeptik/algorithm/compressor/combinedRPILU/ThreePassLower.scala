package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import collection.mutable.{HashMap => MMap, HashSet => MSet}
import collection.Map

abstract class AbstractThreePassLower
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection {

  protected def collectEdgesToDelete(proof: Proof[SequentProofNode],
                                     rootSafeLiterals: IClause,
                                     unitsSafeLiterals: Map[SequentProofNode,IClause]) = {
    val edgesToDelete = new EdgesToDelete()

    def visit(node: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = if (unitsSafeLiterals contains node) {
        edgesToDelete.deleteNode(node)
//        println("Unit " + node.conclusion)
        unitsSafeLiterals(node)
      }
      else if (childrensSafeLiterals == Nil) rootSafeLiterals
      else computeSafeLiterals(node, childrensSafeLiterals, edgesToDelete)

      node match {
        case CutIC(_,right,_,auxR) if (safeLiterals.ant contains auxR) =>
          edgesToDelete.markEdge(node, LeftDS)
        case CutIC(left ,_,auxL,_) if (safeLiterals.suc contains auxL) =>
          edgesToDelete.markEdge(node, RightDS)
        case _ =>
      }

      (node, safeLiterals)
    }

    proof.bottomUp(visit)
    edgesToDelete
  }

}

/* Not equivalent to RPI.LU on :
 * /data/proofs/QG-classification/qg5/iso_icl464.smt2 /data/proofs/QG-classification/qg5/iso_icl395.smt2 /data/proofs/QG-classification/qg5/iso_brn397.smt2 /data/proofs/QG-classification/qg5/iso_icl751.smt2 /data/proofs/QG-classification/qg5/iso_icl048.smt2 /data/proofs/QG-classification/qg5/iso_icl487.smt2 
 */

abstract class ThreePassLowerUnits
extends AbstractThreePassLower {
  protected def collectLowerables(proof: Proof[SequentProofNode]) = {
    val unitsSafeLiterals = MMap[SequentProofNode,IClause]()
    val orderedUnits = scala.collection.mutable.Stack[SequentProofNode]()
    val rootSafeLiterals = proof.foldRight (IClause()) { (node, safeLiterals) =>
      (fakeSize(node.conclusion.ant), fakeSize(node.conclusion.suc), fakeSize(proof.childrenOf(node))) match {
        case (1,0,2) =>
          val literal = node.conclusion.ant(0)
          orderedUnits.push(node)
          unitsSafeLiterals.update(node, literal +: safeLiterals)
          safeLiterals + literal
        case (0,1,2) =>
          val literal = node.conclusion.suc(0)
          orderedUnits.push(node)
          unitsSafeLiterals.update(node, safeLiterals + literal)
          literal +: safeLiterals
        case _ => safeLiterals
      }
    }
    (rootSafeLiterals, orderedUnits, unitsSafeLiterals)
  } 

  def apply(proof: Proof[SequentProofNode]) = {

    // First pass
    val (rootSafeLiterals, orderedUnits, unitsSafeLiterals) = collectLowerables(proof)
//    val nbUnitChildren = orderedUnits.foldLeft(0) { (acc,node) => acc + proof.childrenOf(node).length }
//    println(orderedUnits.length + " orderedUnits with " + nbUnitChildren + " children" )

    // Second pass
    val edgesToDelete = collectEdgesToDelete(proof, rootSafeLiterals, unitsSafeLiterals)

    // Third pass
    if (edgesToDelete.isEmpty) proof else Proof({
      val fixMap = mapFixedProofNodes(orderedUnits.toSet + proof.root, edgesToDelete, proof)
      orderedUnits.foldLeft(fixMap(proof.root)) { (root, unit) =>
        if (unit.conclusion.ant.isEmpty)
          CutIC(fixMap(unit), root, _ == unit.conclusion.suc.head, true)
        else
          CutIC(root, fixMap(unit), _ == unit.conclusion.ant.head, true)
      }
    })
  }

}

object IdempotentThreePassLowerUnits
extends ThreePassLowerUnits with IdempotentAlgorithm[SequentProofNode]
