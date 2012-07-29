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
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection with LeftHeuristic {

  protected def collectUnits(nodeCollection: ProofNodeCollection[SequentProof]):(IClause, Seq[SequentProof], Map[SequentProof,(IClause,IClause)])

  private def collect(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val (rootSafeLiterals, units, unitsMap) = collectUnits(nodeCollection)

    // Protected literals transmited by children aren't the same for the both premises.
    // Hence we need to store them ourself.
    val protectedLiteralMap = MMap[SequentProof,IClause]()
    def addProtectedLiteralFor(proof: SequentProof, literals: IClause) =
      if (!literals.isFalse)
        protectedLiteralMap.update(proof, if (protectedLiteralMap contains proof) protectedLiteralMap(proof) ++ literals else literals)

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      def safeLiteralsFromChild(v:(SequentProof, IClause)) = v match {
        case (p, safeLiterals) if edgesToDelete contains p => safeLiterals
        case (CutIC(left,_,_,auxR),  safeLiterals) if left  == p => safeLiterals + auxR
        case (CutIC(_,right,auxL,_), safeLiterals) if right == p => auxL +: safeLiterals
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      if (unitsMap contains p) {
        deleteFromChildren(p, nodeCollection, edgesToDelete)
        val (efficientLiteral, safeLiterals) = unitsMap(p)
        p.premises.foreach (addProtectedLiteralFor(_, efficientLiteral))
//        println("Unit " + p.conclusion + " " + unitsMap(p))
        (p, safeLiterals)
      }
      else if (childrensSafeLiterals == Nil) (p, rootSafeLiterals)
      else {
        val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
        val protectedLiterals = protectedLiteralMap.getOrElse(p, IClause()) ; protectedLiteralMap.remove(p)
        lazy val leftLiterals  = IClause(p.premises.head.conclusion)
        lazy val rightLiterals = IClause(p.premises.last.conclusion)
        p match {
            case CutIC(_,right,_,auxR) if (safeLiterals.ant contains auxR) && (protectedLiterals -- rightLiterals).isFalse =>
              edgesToDelete.update(p, LeftDS)
              addProtectedLiteralFor(right, protectedLiterals)
            case CutIC(left ,_,auxL,_) if (safeLiterals.suc contains auxL) && (protectedLiterals --  leftLiterals).isFalse =>
              edgesToDelete.update(p, RightDS)
              addProtectedLiteralFor(left, protectedLiterals)
            case CutIC(left,right,pivot,_) =>
              val remainingProtectedLiterals =
                (protectedLiterals -- protectedLiteralMap.getOrElse(left, IClause())) -- protectedLiteralMap.getOrElse(right, IClause())
              if (left.isInstanceOf[Axiom]) {
                var protectedLeft  = remainingProtectedLiterals intersect leftLiterals
                var protectedRight = remainingProtectedLiterals    --     leftLiterals
                if (!protectedLeft.isFalse)  protectedRight = pivot +: protectedRight
                if (!protectedRight.isFalse) protectedLeft  = protectedLeft  +  pivot
                addProtectedLiteralFor(left,  protectedLeft)
                addProtectedLiteralFor(right, protectedRight)
              }
              else {
                var protectedLeft  = remainingProtectedLiterals    --     rightLiterals
                var protectedRight = remainingProtectedLiterals intersect rightLiterals
                if (!protectedLeft.isFalse)  protectedRight = pivot +: protectedRight
                if (!protectedRight.isFalse) protectedLeft  = protectedLeft  +  pivot
                addProtectedLiteralFor(left,  protectedLeft)
                addProtectedLiteralFor(right, protectedRight)
              }
            case _ =>
        }
        (p, safeLiterals)
      }
    }

    nodeCollection.bottomUp(visit)
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
  protected def collectUnits(nodeCollection: ProofNodeCollection[SequentProof]) = {
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
