package skeptik.algorithm.compressor.combinedRPILU

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

class ThreePassLower
extends AbstractRPILUAlgorithm with UnitsCollectingBeforeFixing with CombinedIntersection with LeftHeuristicC {

  private def collectUnits(iterator: ProofNodeCollection[SequentProof]) = {
    val map = MMap[SequentProof, (Set[E],Set[E])]()
    val units = scala.collection.mutable.Stack[SequentProof]()
    val rootSafeLiterals = iterator.foldRight ((Set[E](), Set[E]())) { (p, set) =>
      (fakeSize(p.conclusion.ant), fakeSize(p.conclusion.suc), fakeSize(iterator.childrenOf.getOrElse(p,Nil))) match {
        case (1,0,2) => units.push(p) ; map.update(p, (set._1 + p.conclusion.ant(0), set._2)) ; (set._1, set._2 + p.conclusion.ant(0))
        case (0,1,2) => units.push(p) ; map.update(p, (set._1, set._2 + p.conclusion.suc(0))) ; (set._1 + p.conclusion.suc(0), set._2)
        case _ => set
      }
    }
    (rootSafeLiterals, units, map)
  } 

  private def collect(iterator: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val (rootSafeLiterals, units, unitsMap) = collectUnits(iterator)

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def makeTriple(safeLiterals: (Set[E],Set[E])) = (p, safeLiterals._1, safeLiterals._2)
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      if (unitsMap contains p) {
        deleteFromChildren(p, iterator, edgesToDelete)
//        println("Unit " + p.conclusion + " " + unitsMap(p))
        makeTriple(unitsMap(p))
      }
      else if (childrensSafeLiterals == Nil) makeTriple(rootSafeLiterals)
      else {
        val (safeL,safeR) = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
        p match {
            case CutIC(_,_,_,auxR) if safeL contains auxR => edgesToDelete.update(p, LeftDS)
            case CutIC(_,_,auxL,_) if safeR contains auxL => edgesToDelete.update(p, RightDS)
            case _ => Unit
        }
        (p, safeL, safeR)
      }
    }

    iterator.bottomUp(visit)
//    units.foreach (deleteFromChildren(_, iterator, edgesToDelete))
    (units, edgesToDelete)
  }

  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val (units, edgesToDelete) = collect(iterator)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, iterator)
      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }
}
