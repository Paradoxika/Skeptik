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
   * nodes, a map from lowered node to its efficient literal and the safe
   * literals.
   */
  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]):(IClause, Seq[SequentProof], Map[SequentProof,(IClause,IClause)])

  private def collect(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val (rootSafeLiterals, units, unitsMap) = collectLowerables(nodeCollection)

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      def safeLiteralsFromChild(v:(SequentProof, IClause)) = v match {
        case (p, safeLiterals) if edgesToDelete contains p => safeLiterals
        case (CutIC(left,_,_,auxR),  safeLiterals) if left  == p => safeLiterals + auxR
        case (CutIC(_,right,auxL,_), safeLiterals) if right == p => auxL +: safeLiterals
        case _ => throw new Exception("Unknown or impossible inference rule")
      }

      // Node is lowerable
      if (unitsMap contains p) {
        deleteFromChildren(p, nodeCollection, edgesToDelete)
        val (efficientLiteral, safeLiterals) = unitsMap(p)
//        println("Unit " + p.conclusion + " " + unitsMap(p))
        (p, safeLiterals)
      }

      // Root node
      else if (childrensSafeLiterals == Nil) (p, rootSafeLiterals)

      else {
        val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
        p match {
            case CutIC(_,_,_,auxR) if safeLiterals.ant contains auxR => edgesToDelete.update(p, LeftDS)
            case CutIC(_,_,auxL,_) if safeLiterals.suc contains auxL => edgesToDelete.update(p, RightDS)
            case _ =>
        }
        (p, safeLiterals)
      }
    }

    nodeCollection.bottomUp(visit)
    (units, unitsMap, edgesToDelete)
  }



  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val (units, unitMap, edgesToDelete) = collect(nodeCollection)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, nodeCollection)
//      for (k <- units) {
//        val v = fixMap(k)
//        if (k.conclusion == v.conclusion)
//          println("I " + k.conclusion)
//        else
//          println("C " + k.conclusion + " -> " + v.conclusion)
//      }
      def repair(unit: SequentProof) = {
        val fixed = fixMap(unit)
        if ((IClause(fixed.conclusion) intersect unitMap(unit)._1).isFalse) { println("R " + unit.conclusion) ; unit } else fixed
      }
      units.map(repair).foldLeft(fixMap(proof)) { (left,right) =>
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }
}

class ThreePassLower
extends AbstractThreePassLower {
  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val map = MMap[SequentProof, (IClause,IClause)]()
    val units = scala.collection.mutable.Stack[SequentProof]()
    val rootSafeLiterals = nodeCollection.foldRight (IClause()) { (p, safeLiterals) =>
      (fakeSize(p.conclusion.ant), fakeSize(p.conclusion.suc), fakeSize(nodeCollection.childrenOf(p))) match {
        // TODO : should I add the unit's literal to safeLiterals to be transmited to unit's premises ?
        case (1,0,2) =>
          val literal = p.conclusion.ant(0)
          units.push(p)
          map.update(p, (new IClause(Set[E](literal),Set[E]()), safeLiterals))
          safeLiterals + literal
        case (0,1,2) =>
          val literal = p.conclusion.suc(0)
          units.push(p)
          map.update(p, (new IClause(Set[E](),Set[E](literal)), safeLiterals))
          literal +: safeLiterals
        case _ => safeLiterals
      }
    }
    (rootSafeLiterals, units, map)
  } 
}
