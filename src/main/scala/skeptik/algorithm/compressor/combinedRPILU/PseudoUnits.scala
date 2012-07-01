package skeptik.algorithm.compressor.combinedRPILU

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

object pseudoUnits {

  abstract class CheckResult
  case class IsPseudoUnit (val literal: Either[E,E])  extends CheckResult
  object NotPseudoUnit extends CheckResult
  object CanBeDeleted  extends CheckResult

  class CheckIfPseudoUnit
  {

    val literalsDeletedByUnits = (MSet[E](),MSet[E]())

    private def append(proof: SequentProof, literal: Either[E,E]) = {
      // println("+ " + proof.conclusion + " " + literal)
      literal match {
        case Left(v)  => literalsDeletedByUnits._1.add(v)
        case Right(v) => literalsDeletedByUnits._2.add(v)
      }
      IsPseudoUnit(literal)
    }

    def apply(newProof: SequentProof, oldProof: SequentProof, children: List[SequentProof]):CheckResult = {
      val literals = literalsIntroducedByDeletion(newProof, oldProof, children)
  //      println("Remaining Literals " + literals)
      (literals._1.size, literals._2.size) match {
        case (0,0) => CanBeDeleted
        case (0,1) => checkLiteralsIntroducedByLowering(newProof, Left(literals._2.head))
        case (1,0) => checkLiteralsIntroducedByLowering(newProof, Right(literals._1.head))
        case _ => NotPseudoUnit
      }
    }
    def apply(proof: SequentProof, children: List[SequentProof]):CheckResult =
        apply(proof, proof, children)

    private def literalsIntroducedByDeletion(newProof: SequentProof, oldProof: SequentProof, children: Seq[SequentProof]) = {
      val literalsIntroducedByDeletion =
        children.foldLeft((Set[E](),Set[E]())) { (setPair, child) =>
          child match {
            case CutIC(left, right, aux, _) if left  == oldProof => (setPair._1 + aux, setPair._2)
            case CutIC(left, right, aux, _) if right == oldProof => (setPair._1, setPair._2 + aux)
            case _ => setPair
          }
        }
        (literalsIntroducedByDeletion._1 diff literalsDeletedByUnits._2,
          literalsIntroducedByDeletion._2 diff literalsDeletedByUnits._1)
    }

    private def checkLiteralsIntroducedByLowering(proof: SequentProof, remainingLiteral: Either[E,E]) = {
      val (leftLiterals, rightLiterals) = (proof.conclusion.ant.toSet diff literalsDeletedByUnits._2,
                                          proof.conclusion.suc.toSet diff literalsDeletedByUnits._1)
      (leftLiterals.size, rightLiterals.size, remainingLiteral) match {
        case (1,0,Left(literal))  if leftLiterals.head  == literal => append(proof, remainingLiteral)
        case (0,1,Right(literal)) if rightLiterals.head == literal => append(proof, remainingLiteral)
        case _ => NotPseudoUnit
      }
    }

  } // class CheckIfPseudoUnit
} // object pseudoUnits

import pseudoUnits._

abstract class AbstractPseudoUnitsNotDuringFixing
extends AbstractRPILUAlgorithm with LeftHeuristicC {
  def fixProofAndUnits(iterator: ProofNodeCollection[SequentProof],
                       edgesToDelete: MMap[SequentProof,DeletedSide],
                       unitMap: Map[SequentProof,LList[SequentProof]]) = {
    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      if (unitMap contains oldProof) {
        unitMap(oldProof).elem = newProof
        deleteFromChildren(oldProof, iterator, edgesToDelete)
      }
      newProof
    }
    iterator.foldDown(reconstructProof _)
  }
}

class PseudoUnits (minNumberOfChildren: Int)
// TODO: remove CombinedIntersection and made PseudoUnits a subclass of a class more general than AbstractRPILUAlgorithm
extends AbstractPseudoUnitsNotDuringFixing with CombinedIntersection {
  def collectUnits(iterator: ProofNodeCollection[SequentProof]) = {
    val isPseudoUnit = new CheckIfPseudoUnit()
    var units   = LList[SequentProof]()
    val unitMap = MMap[SequentProof, LList[SequentProof]]()
    iterator.foreachDown { (p) =>
      val children = iterator.childrenOf.getOrElse(p, Nil)
      if (fakeSize(children) >= minNumberOfChildren) {
        isPseudoUnit(p, children) match {
          case IsPseudoUnit(_) =>
            units = new LList(p, units)
            unitMap.update(p, units)
          case _ => Unit
        }
      }
    }
    (units, unitMap)
  }

  def apply(proof: SequentProof) = {
    val iterator = ProofNodeCollection(proof)
    val (units, unitMap) = collectUnits(iterator)
    val pseudoRoot = fixProofAndUnits(iterator, MMap[SequentProof,DeletedSide](), unitMap)
//    println("root " + pseudoRoot.conclusion)
//    println("units " + units.map(_.conclusion))
    units.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}

abstract class AbstractPseudoUnitsDuringFixing (minNumberOfChildren: Int)
extends AbstractRPILUAlgorithm with LeftHeuristicC {
  def fixProofAndLowerUnits(iterator: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) = {

    var units = List[SequentProof]()
    val isPseudoUnit = new CheckIfPseudoUnit()

    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      val children = iterator.childrenOf.getOrElse(oldProof,Nil) filter { child => !childIsMarkedToDeleteParent(child, oldProof, edgesToDelete) }
      if (fakeSize(children) >= minNumberOfChildren) isPseudoUnit(newProof, oldProof, children) match {
        case IsPseudoUnit(_) => units ::= newProof ; deleteFromChildren(oldProof, iterator, edgesToDelete)
        case CanBeDeleted => deleteFromChildren(oldProof, iterator, edgesToDelete)
        case _ => Unit
      }
      newProof
    }

    val pseudoRoot = iterator.foldDown(reconstructProof _)
//    println("root " + pseudoRoot.conclusion)
//    println("units " + units.map(_.conclusion))
    units.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}

class OnePassPseudoUnits (minNumberOfChildren: Int)
// TODO: remove CombinedIntersection
extends AbstractPseudoUnitsDuringFixing(minNumberOfChildren) with CombinedIntersection {
  def apply(proof: SequentProof): SequentProof =
    fixProofAndLowerUnits(ProofNodeCollection(proof), MMap[SequentProof,DeletedSide]())
}


class PseudoUnitsAfter (minNumberOfChildren: Int)
extends AbstractPseudoUnitsDuringFixing(minNumberOfChildren) with EdgesCollectingUsingSafeLiterals with CombinedIntersection {
  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(iterator)
    fixProofAndLowerUnits(iterator, edgesToDelete)
  }
}

class PseudoUnitsBefore (minNumberOfChildren: Int)
extends AbstractRPILUAlgorithm with UnitsCollectingBeforeFixing with CombinedIntersection with LeftHeuristicC {
// TODO: share code with ThreePassUnit

  private def collectUnits(iterator: ProofNodeCollection[SequentProof]) = {
    val isPseudoUnit = new CheckIfPseudoUnit()
    var units = List[SequentProof]()
    val map = MMap[SequentProof, (Set[E],Set[E])]()
    val rootSafeLiterals = iterator.foldRight ((Set[E](), Set[E]())) { (p, set) =>
      val children = iterator.childrenOf.getOrElse(p,Nil)
      if (fakeSize(children) < minNumberOfChildren) set else
        isPseudoUnit(p, children) match {
          case IsPseudoUnit(Left(l))  => println("+ " + p.conclusion + " L " + l) ; units ::= p ; map.update(p,set) ; (set._1, set._2 + l)
          case IsPseudoUnit(Right(l)) => println("+ " + p.conclusion + " R " + l) ; units ::= p ; map.update(p,set) ; (set._1 + l, set._2)
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
        println("Unit " + p.conclusion + " " + unitsMap(p))
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
    (units, edgesToDelete)
  }

  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val (units, edgesToDelete) = collect(iterator)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, iterator)
      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
        println("We have got   " + left.conclusion)
        println("Reintroducing " + right.conclusion)
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }

}
