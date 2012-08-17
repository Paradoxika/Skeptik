package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import collection.mutable.{HashMap => MMap, HashSet => MSet}
import collection.Map

abstract class AbstractThreePassLower
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection {

  protected def collectEdgesToDelete(proof: ProofNodeCollection[SequentProof],
                                     rootSafeLiterals: IClause,
                                     unitsSafeLiterals: Map[SequentProof,IClause]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()

    def visit(node: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      val safeLiterals = if (unitsSafeLiterals contains node) {
        deleteFromChildren(node, proof, edgesToDelete)
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

    proof.bottomUp(visit)
    edgesToDelete
  }

}


abstract class ThreePassLowerUnits
extends AbstractThreePassLower {
  protected def collectLowerables(proof: ProofNodeCollection[SequentProof]) = {
    val unitsSafeLiterals = MMap[SequentProof,IClause]()
    val orderedUnits = scala.collection.mutable.Stack[SequentProof]()
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

  def apply(proof: ProofNodeCollection[SequentProof]) = {

    // First pass
    val (rootSafeLiterals, orderedUnits, unitsSafeLiterals) = collectLowerables(proof)
//    val nbUnitChildren = orderedUnits.foldLeft(0) { (acc,node) => acc + proof.childrenOf(node).length }
//    println(orderedUnits.length + " orderedUnits with " + nbUnitChildren + " children" )

    // Second pass
    val edgesToDelete = collectEdgesToDelete(proof, rootSafeLiterals, unitsSafeLiterals)
//    println(edgesToDelete.size + " edges to delete (" + (edgesToDelete.size - nbUnitChildren) + " without orderedUnits' children)")

    // Third pass
    if (edgesToDelete.isEmpty) proof else ProofNodeCollection({
      val fixMap = mapFixedProofs(orderedUnits.toSet + proof.root, edgesToDelete, proof)
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
extends ThreePassLowerUnits with IdempotentAlgorithm[SequentProof]
