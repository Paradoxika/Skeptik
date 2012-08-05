package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.Map

abstract class AbstractThreePassLower
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection {

  protected def collectEdgesToDelete(nodeCollection: ProofNodeCollection[SequentProof],
                                     rootSafeLiterals: IClause,
                                     unitsSafeLiterals: Map[SequentProof,IClause]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()

    def visit(node: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      val safeLiterals = if (unitsSafeLiterals contains node) {
        deleteFromChildren(node, nodeCollection, edgesToDelete)
//        println("Unit " + node.conclusion)
        unitsSafeLiterals(node)
      }
      else if (childrensSafeLiterals == Nil) rootSafeLiterals
      else computeSafeLiterals(node, childrensSafeLiterals, edgesToDelete)

      node match {
        case CutIC(_,right,_,auxR) if (safeLiterals.ant contains auxR) =>
          edgesToDelete.update(node, LeftDS)
        case CutIC(left ,_,auxL,_) if (safeLiterals.suc contains auxL) =>
          edgesToDelete.update(node, RightDS)
        case _ =>
      }

      (node, safeLiterals)
    }

    nodeCollection.bottomUp(visit)
    edgesToDelete
  }

}


class ThreePassLower
extends AbstractThreePassLower {

  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val unitsSafeLiterals = MMap[SequentProof,IClause]()
    val orderedUnits = scala.collection.mutable.Stack[SequentProof]()
    val rootSafeLiterals = nodeCollection.foldRight (IClause()) { (node, safeLiterals) =>
      (fakeSize(node.conclusion.ant), fakeSize(node.conclusion.suc), fakeSize(nodeCollection.childrenOf(node))) match {
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

  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)

    // First pass
    val (rootSafeLiterals, orderedUnits, unitsSafeLiterals) = collectLowerables(nodeCollection)
//    val nbUnitChildren = orderedUnits.foldLeft(0) { (acc,node) => acc + nodeCollection.childrenOf(node).length }
//    println(orderedUnits.length + " orderedUnits with " + nbUnitChildren + " children" )

    // Second pass
    val edgesToDelete = collectEdgesToDelete(nodeCollection, rootSafeLiterals, unitsSafeLiterals)
//    println(edgesToDelete.size + " edges to delete (" + (edgesToDelete.size - nbUnitChildren) + " without orderedUnits' children)")

    // Third pass
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(orderedUnits.toSet + proof, edgesToDelete, nodeCollection)
      orderedUnits.foldLeft(fixMap(proof)) { (root, unit) =>
        if (unit.conclusion.ant.isEmpty)
          CutIC(fixMap(unit), root, _ == unit.conclusion.suc.head, true)
        else
          CutIC(root, fixMap(unit), _ == unit.conclusion.ant.head, true)
      }
    }
  }

}
