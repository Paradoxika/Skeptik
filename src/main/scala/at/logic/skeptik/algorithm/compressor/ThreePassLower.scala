package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import collection.mutable.{HashMap => MMap, HashSet => MSet, Stack}
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
          unitsSafeLiterals(node)
        }
        else if (childrensSafeLiterals == Nil) rootSafeLiterals
        else computeSafeLiterals(node, childrensSafeLiterals, edgesToDelete)

      node match {
        case R(_,right,_,auxR) if (safeLiterals.ant contains auxR) =>
          edgesToDelete.markLeftEdge(node)
        case R(left ,_,auxL,_) if (safeLiterals.suc contains auxL) =>
          edgesToDelete.markRightEdge(node)
        case _ =>
      }

      (node, safeLiterals)
    }

    proof.bottomUp(visit)
    edgesToDelete
  }

}

object IdempotentThreePassLowerUnits
extends AbstractThreePassLower {
  protected def collectLowerables(proof: Proof[SequentProofNode]) = {
    val unitsSafeLiterals = MMap[SequentProofNode,IClause]()
    val orderedUnits = Stack[SequentProofNode]()
    val rootSafeLiterals = proof.foldRight(IClause()) { (node, safeLiterals) =>
      (node.conclusion.ant.length, node.conclusion.suc.length, proof.childrenOf(node).length) match {
        case (1,0,s) if s >= 2 =>
          val literal = node.conclusion.ant(0)
          orderedUnits.push(node)
          unitsSafeLiterals(node) = (literal +: safeLiterals)
          safeLiterals + literal
        case (0,1,s) if s >= 2 =>
          val literal = node.conclusion.suc(0)
          orderedUnits.push(node)
          unitsSafeLiterals(node) = (safeLiterals + literal)
          literal +: safeLiterals
        case _ => safeLiterals
      }
    }
    (rootSafeLiterals, orderedUnits, unitsSafeLiterals)
  } 

  def apply(proof: Proof[SequentProofNode]) = {

    // First pass
    val (rootSafeLiterals, orderedUnits, unitsSafeLiterals) = collectLowerables(proof)

    // Second pass
    val edgesToDelete = collectEdgesToDelete(proof, rootSafeLiterals, unitsSafeLiterals)

    // Third pass
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofNodes(orderedUnits.toSet + proof.root, edgesToDelete, proof)
      orderedUnits.foldLeft(fixMap(proof.root)) { (root, unit) =>
        if (unit.conclusion.ant.isEmpty)
          R(fixMap(unit), root, unit.conclusion.suc.head, true)
        else
          R(root, fixMap(unit), unit.conclusion.ant.head, true)
      }
    }
  }

}
