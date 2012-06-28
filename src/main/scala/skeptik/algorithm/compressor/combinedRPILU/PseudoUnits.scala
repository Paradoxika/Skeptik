package skeptik.algorithm.compressor.combinedRPILU

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

class PseudoUnitsList {

  // Ordered list of (pseudo-)units
  private var units = LList[(Either[E,E],SequentProof)]()
  // The maximum size (nb of literal in conclusion) for a proof to be added to units
  private var unitsLimit = 1
  private val literalsDeletedByUnits = (MSet[E](),MSet[E]())

  private def updateDataAfterAdding(literal: Either[E,E]) = {
    unitsLimit += 1
    literal match {
      case Left(v)  => literalsDeletedByUnits._1.add(v)
      case Right(v) => literalsDeletedByUnits._2.add(v)
    }
  }

  private def prependUnit(proof: SequentProof, literal: Either[E,E]) = {
//      println("- " + proof.conclusion)
    units = new LList((literal, proof), units)
    updateDataAfterAdding(literal)
    Some(units)
  }

  private def insertUnitAfter(proof: SequentProof, literal: Either[E,E], node: LList[(Either[E,E],SequentProof)]) = {
//      println("+ " + proof.conclusion + " (" + literal + ")")
    node.next = new LList((literal, proof), node.next)
    updateDataAfterAdding(literal)
    Some(node.next)
  }

  def addIfPseudoUnit(newProof: SequentProof, oldProof: SequentProof, children: List[SequentProof]):Option[LList[(Either[E,E],SequentProof)]] = {
    val literals = literalsIntroducedByDeletion(newProof, oldProof, children)
//      println("Remaining Literals " + literals)
    (literals._1.size, literals._2.size) match {
      case (0,0) => Some(LList((Left(Var("fake",i)),oldProof))) // proof can be safely deleted
      case (0,1) => checkLiteralsIntroducedByLowering(newProof, Left(literals._2.head))
      case (1,0) => checkLiteralsIntroducedByLowering(newProof, Right(literals._1.head))
      case _ => None
    }
  }
  def addIfPseudoUnit(proof: SequentProof, children: List[SequentProof]):Option[LList[(Either[E,E],SequentProof)]] =
      addIfPseudoUnit(proof, proof, children)

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
    val (leftLiterals, rightLiterals) = (proof.conclusion.ant.toSet, proof.conclusion.suc.toSet)
    (leftLiterals.size, rightLiterals.size) match {
      case (1,0) => prependUnit(proof, Left(leftLiterals.head))
      case (0,1) => prependUnit(proof, Right(rightLiterals.head))
      case (l,r) if (l+r <= unitsLimit) => insertUnit(proof, (leftLiterals, rightLiterals), l+r, remainingLiteral)
      case _ => None
    }
  }

  private def insertUnit(proof: SequentProof, literals: (Set[E],Set[E]), size: Int, remainingLiteral: Either[E,E]) = {
  // This function scans the units list for insertion, introducing quadratic complexity.

    // invariant : size <= limit
    def recursiveScan(oldLit: (Set[E],Set[E]),
                      size: Int,
                      node: LList[(Either[E,E],SequentProof)],
                      limit: Int)                             :Option[LList[(Either[E,E],SequentProof)]] = {
      val newLit = node.elem._1 match {
        case Left(l)  => (oldLit._1, oldLit._2 - l)
        case Right(r) => (oldLit._1 - r, oldLit._2)
      }
//        println("Scan " + oldLit + " node " + node.elem._1 + " size " + size + " limit " + limit)
      (newLit._1.size, newLit._2.size, remainingLiteral) match {
        case (1,0,Left(literal))  if literal == newLit._1.head => insertUnitAfter(proof, remainingLiteral, node)
        case (0,1,Right(literal)) if literal == newLit._2.head => insertUnitAfter(proof, remainingLiteral, node)
        case (l,r,_)             if (l+r > 1) && (l+r < limit) => recursiveScan(newLit, l+r, node.next, limit-1)
        case _ => None
      }
    }

    recursiveScan(literals, size, units, unitsLimit)
  }

  def unitList = units.foldLeft(List[SequentProof]()) { (lst,u) => (u._2)::lst }

} // class PseudoUnitsList

class PseudoUnitsAfter (minNumberOfChildren: Int)
extends AbstractRPILUAlgorithm with EdgesCollectingUsingSafeLiterals with CombinedIntersection with LeftHeuristicC {

  private def fixProofAndLowerUnits(iterator: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) = {

    val pseudoUnitList = new PseudoUnitsList()

    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      val children = iterator.childrenOf.getOrElse(oldProof,Nil) filter { child => !childIsMarkedToDeleteParent(child, oldProof, edgesToDelete) }
      if (fakeSize(children) >= minNumberOfChildren && pseudoUnitList.addIfPseudoUnit(newProof, oldProof, children).isDefined)
        deleteFromChildren(oldProof, iterator, edgesToDelete)
      newProof
    }

    val pseudoRoot = iterator.foldDown(reconstructProof _)
//    println("root " + pseudoRoot.conclusion)
    (pseudoRoot, pseudoUnitList.unitList)
  }

  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(iterator)
    val (pseudoRoot, units) = fixProofAndLowerUnits(iterator, edgesToDelete)
//    println("Units : " + units.map{_.conclusion})
    units.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}
