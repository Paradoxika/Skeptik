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

  /** Collect nodes to be lowered
   *
   * This is the fist pass of the algorithm.
   *
   * Nodes collected by this function should have at most one pivot candidate
   * when reintroduced.
   *
   * @return The lowered literals clause, the ordered sequence of lowered
   * nodes, a map from lowered node to its safe literals.
   */
  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]):(IClause, Seq[SequentProof], Map[SequentProof,IClause])

  protected def collectEdgesToDelete(nodeCollection: ProofNodeCollection[SequentProof],
                                     rootSafeLiterals: IClause,
                                     unitsMap: Map[SequentProof,IClause]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()

    def visit(node: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      val safeLiterals = if (unitsMap contains node) {
        deleteFromChildren(node, nodeCollection, edgesToDelete)
//        println("Unit " + node.conclusion)
        unitsMap(node)
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



  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)

    // First pass
    val (rootSafeLiterals, units, unitsMap) = collectLowerables(nodeCollection)
//    val nbUnitChildren = units.foldLeft(0) { (acc,node) => acc + nodeCollection.childrenOf(node).length }
//    println(units.length + " units with " + nbUnitChildren + " children" )

    // Second pass
    val edgesToDelete = collectEdgesToDelete(nodeCollection, rootSafeLiterals, unitsMap)
//    println(edgesToDelete.size + " edges to delete (" + (edgesToDelete.size - nbUnitChildren) + " without units' children)")

    // Third pass
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, nodeCollection)
      units.foldLeft(fixMap(proof)) { (root, unit) =>
        if (unit.conclusion.ant.isEmpty)
          CutIC(fixMap(unit), root, _ == unit.conclusion.suc.head, true)
        else
          CutIC(root, fixMap(unit), _ == unit.conclusion.ant.head, true)
      }
    }
  }
}


class ThreePassLower
extends AbstractThreePassLower {

  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val map = MMap[SequentProof,IClause]()
    val units = scala.collection.mutable.Stack[SequentProof]()
    val rootSafeLiterals = nodeCollection.foldRight (IClause()) { (node, safeLiterals) =>
      (fakeSize(node.conclusion.ant), fakeSize(node.conclusion.suc), fakeSize(nodeCollection.childrenOf(node))) match {
        case (1,0,2) =>
          val literal = node.conclusion.ant(0)
          units.push(node)
          map.update(node, literal +: safeLiterals)
          safeLiterals + literal
        case (0,1,2) =>
          val literal = node.conclusion.suc(0)
          units.push(node)
          map.update(node, safeLiterals + literal)
          literal +: safeLiterals
        case _ => safeLiterals
      }
    }
    (rootSafeLiterals, units, map)
  } 
}
