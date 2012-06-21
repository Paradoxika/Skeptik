package skeptik.algorithm.compressor.combinedRPILU

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map


abstract class PseudoUnitsAfter
extends AbstractRPILUAlgorithm with LeftHeuristicC {

  def collectEdgesToDelete(iterator: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      val (safeL,safeR) = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
      p match {
        case CutIC(_,_,auxL,_) if safeR contains auxL => edgesToDelete.update(p, RightDS)
        case CutIC(_,_,_,auxR) if safeL contains auxR => edgesToDelete.update(p, LeftDS)
        case _ => Unit
      }
      (p, safeL, safeR)
    }
    iterator.bottomUp(visit)
    edgesToDelete
  }

  private def fixProofAndLowerUnits(iterator: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) = {

    // Ordered list of (pseudo-)units
    var units = LList[(Either[E,E],SequentProof)]()
    // The maximum size (nb of literal in conclusion) for a proof to be added to units
    var unitsLimit = 1
    val literalsDeletedByUnits = (MSet[E](),MSet[E]())

    def afterInsert(oldProof: SequentProof, literal: Either[E,E]) = {
      unitsLimit += 1
      literal match {
        case Left(v)  => literalsDeletedByUnits._1.add(v)
        case Right(v) => literalsDeletedByUnits._2.add(v)
      }
      deleteFromChildren(oldProof, iterator, edgesToDelete)
    }

    // This function scans the units list for insertion, introducing quadratic complexity.
    def scanUnit(oldProof: SequentProof, newProof: SequentProof, introducedLiteral: Either[E,E],
                 literals: (Set[E],Set[E]), size: Int) = {

      def insertUnit(literal: Either[E,E], node: LList[(Either[E,E],SequentProof)]) =
        if (literal == introducedLiteral) {
          node.next = new LList((literal,  newProof), node.next)
          afterInsert(oldProof, literal)
//          println("+ " + newProof.conclusion + " (" + literal + ")")
        }

      // invariant : size <= limit
      def scan(oldLit: (Set[E],Set[E]), size: Int, node: LList[(Either[E,E],SequentProof)], limit: Int):Unit = {
        val newLit = node.elem._1 match {
          case Left(l)  => (oldLit._1, oldLit._2 - l)
          case Right(r) => (oldLit._1 - r, oldLit._2)
        }
        (newLit._1.size, newLit._2.size) match {
          case (1,0) => insertUnit(Left(newLit._1.head),  node)
          case (0,1) => insertUnit(Right(newLit._2.head), node)
          case (l,r) => if (l+r < limit) scan(newLit, l+r, node.next, limit - 1)
        }
      }

      scan(literals, size, units, unitsLimit)
    }

    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
//      if (isUnit(oldProof,iterator)) println("unit " + oldProof.conclusion + " => " + newProof.conclusion)
      def prependUnit(literal: Either[E,E]) = {
        units = new LList((literal, newProof), units)
        afterInsert(oldProof, literal)
//        println("- " + newProof.conclusion)
      }

      val children = iterator.childrenOf.getOrElse(oldProof, Nil)
      if (fakeSize(children) > 1) {
        // For a node to be lowered we check two conditions which are coded reverse

        // Second condition : literals introduced by lowering the proof node get resolved by preceding units (except one)
        def checkLoweredLiteralGetResolved(remainingLiteral: Either[E,E]) = {
          val literalsIntroducedBylowering = (newProof.conclusion.ant.toSet, newProof.conclusion.suc.toSet)
          (literalsIntroducedBylowering._1.size, literalsIntroducedBylowering._2.size) match {
            case (1,0) => prependUnit(Left(literalsIntroducedBylowering._1.head))
            case (0,1) => prependUnit(Right(literalsIntroducedBylowering._2.head))
            case (l,r) => if (l+r <= unitsLimit) scanUnit(oldProof, newProof, remainingLiteral,
                                                          literalsIntroducedBylowering, l+r)
          }
        }

        // First condition : literals introduced by deleting the proof node from its current positions
        // get resolved by current units (except one)
        val literalsIntroducedByDeletion =
          children.foldLeft((Set[E](),Set[E]())) { (setPair, child) =>
            child match {
              case CutIC(left, right, auxL, auxR) if left  == oldProof => (setPair._1 + auxR, setPair._2)
              case CutIC(left, right, auxL, auxR) if right == oldProof => (setPair._1, setPair._2 + auxL)
              case _ => throw new Exception("Unable to find parent as premise of child")
            }
          }
        val literalsRemainingFromDeletion =
          (literalsIntroducedByDeletion._1 diff literalsDeletedByUnits._2,
           literalsIntroducedByDeletion._2 diff literalsDeletedByUnits._1)

        (literalsRemainingFromDeletion._1.size, literalsRemainingFromDeletion._2.size) match {
          case (0,0) => deleteFromChildren(oldProof, iterator, edgesToDelete)
          case (1,0) => checkLoweredLiteralGetResolved(Right(literalsRemainingFromDeletion._1.head))
          case (0,1) => checkLoweredLiteralGetResolved(Left(literalsRemainingFromDeletion._2.head))
          case _ => Unit
        }
      }
      newProof
    }

    val pseudoRoot = iterator.foldDown(reconstructProof _)
//    println("root " + pseudoRoot.conclusion)
//    println("units " + (units.map(_._1 match { case Left(v) => v ; case Right(v) => v })))
    val orderedUnits = units.foldLeft(List[SequentProof]()) { (lst,u) => (u._2)::lst }
    (pseudoRoot, orderedUnits)
  }

  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(iterator) // TODO: mix this line with the next one
    val (pseudoRoot, units) = fixProofAndLowerUnits(iterator, edgesToDelete)
    units.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}

// TODO: Refactor class and traits hierarchie between LU, RPI and Combined.
class PseudoUnitsBeforeAndAfter
extends PseudoUnitsAfter {
  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, Set[E], Set[E])) => (Set[E],Set[E])
                          ) : (Set[E],Set[E]) =
    throw new Exception("This function should never be called")
  
  override def collectEdgesToDelete(iterator: ProofNodeCollection[SequentProof]) = {
    var (unitsLiteralsL, unitsLiteralsR) = (Set[E](),Set[E]())
    val edgesToDelete = MMap[SequentProof,DeletedSide]()

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }

      var (safeL,safeR) = childrensSafeLiterals.filter { x => !childIsMarkedToDeleteParent(x._1, p, edgesToDelete)} match {
        case Nil  => iterator.foldLeft((Set[E](p.conclusion.ant:_*), Set[E](p.conclusion.suc:_*))) { (acc, p) =>
          (fakeSize(p.conclusion.ant), fakeSize(p.conclusion.suc), fakeSize(iterator.childrenOf.getOrElse(p,Nil))) match {
            case (1,0,2) => (acc._1, acc._2 + p.conclusion.ant(0))
            case (0,1,2) => (acc._1 + p.conclusion.suc(0), acc._2)
            case _ => acc
          }
        }
        case h::t => t.foldLeft(safeLiteralsFromChild(h)) { (acc, v) =>
          val (sL, sR) = safeLiteralsFromChild(v)
          (acc._1 intersect sL, acc._2 intersect sR)
        }
      }

      (fakeSize(p.conclusion.ant), fakeSize(p.conclusion.suc), fakeSize(iterator.childrenOf.getOrElse(p,Nil))) match {
        case (1,0,2) => safeR = safeR intersect unitsLiteralsR ; unitsLiteralsR += p.conclusion.ant(0)
        case (0,1,2) => safeL = safeL intersect unitsLiteralsL ; unitsLiteralsL += p.conclusion.suc(0)
        case _ => Unit
      }

      p match {
        case CutIC(_,right,auxL,_) if (safeR contains auxL) && !isUnit(right,iterator) => edgesToDelete.update(p, RightDS)
        case CutIC(left,_,_,auxR)  if (safeL contains auxR) && !isUnit(left,iterator) => edgesToDelete.update(p, LeftDS)
        case _ => Unit
      }
      (p, safeL, safeR)
    }
    iterator.bottomUp(visit)
//    println("Left  " + unitsLiteralsL)
//    println("Right " + unitsLiteralsR)
    edgesToDelete
  }

}
