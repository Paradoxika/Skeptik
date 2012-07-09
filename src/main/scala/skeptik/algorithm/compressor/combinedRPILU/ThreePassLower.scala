package skeptik.algorithm.compressor
package combinedRPILU

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.judgment.immutable.{SetSequent => IClause}
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.Map

abstract class AbstractThreePassLower
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection with LeftHeuristic {

  def collectUnits(nodeCollection: ProofNodeCollection[SequentProof]):(IClause, Seq[SequentProof], Map[SequentProof,IClause])

  private def collect(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val (rootSafeLiterals, units, unitsMap) = collectUnits(nodeCollection)

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      def safeLiteralsFromChild(v:(SequentProof, IClause)) = v match {
        case (p, safeLiterals) if edgesToDelete contains p => safeLiterals
        case (CutIC(left,_,_,auxR),  safeLiterals) if left  == p => safeLiterals + auxR
        case (CutIC(_,right,auxL,_), safeLiterals) if right == p => auxL +: safeLiterals
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      if (unitsMap contains p) {
        deleteFromChildren(p, nodeCollection, edgesToDelete)
//        println("Unit " + p.conclusion + " " + unitsMap(p))
        (p, unitsMap(p))
      }
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
//    units.foreach (deleteFromChildren(_, nodeCollection, edgesToDelete))
    (units, edgesToDelete)
  }

  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val (units, edgesToDelete) = collect(nodeCollection)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, nodeCollection)
      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }
}

class ThreePassLower
extends AbstractThreePassLower {
  def collectUnits(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val map = MMap[SequentProof, IClause]()
    val units = scala.collection.mutable.Stack[SequentProof]()
    val rootSafeLiterals = nodeCollection.foldRight (IClause()) { (p, safeLiterals) =>
      (fakeSize(p.conclusion.ant), fakeSize(p.conclusion.suc), fakeSize(nodeCollection.childrenOf(p))) match {
        // TODO : should I add the unit's literal to safeLiterals to be transmited to unit's premises ?
        case (1,0,2) => units.push(p) ; map.update(p, safeLiterals) ; safeLiterals + p.conclusion.ant(0)
        case (0,1,2) => units.push(p) ; map.update(p, safeLiterals) ; p.conclusion.suc(0) +: safeLiterals
        case _ => safeLiterals
      }
    }
    (rootSafeLiterals, units, map)
  } 
}
