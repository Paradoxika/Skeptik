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
  private var lastLL = units
  // The maximum size (nb of literal in conclusion) for a proof to be added to units
  private val literalsDeletedByUnits = (MSet[E](),MSet[E]())

  private def append(proof: SequentProof, literal: Either[E,E]) = {
//    println("+ " + proof.conclusion + " " + literal)
    literal match {
      case Left(v)  => literalsDeletedByUnits._1.add(v)
      case Right(v) => literalsDeletedByUnits._2.add(v)
    }
    val ret = lastLL
    ret.elem = (literal, proof)
    ret.next = LList[(Either[E,E],SequentProof)]()
    lastLL = ret.next
    Some(ret)
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
    val (leftLiterals, rightLiterals) = (proof.conclusion.ant.toSet diff literalsDeletedByUnits._2,
                                         proof.conclusion.suc.toSet diff literalsDeletedByUnits._1)
    (leftLiterals.size, rightLiterals.size, remainingLiteral) match {
      case (1,0,Left(literal))  if leftLiterals.head  == literal => append(proof, remainingLiteral)
      case (0,1,Right(literal)) if rightLiterals.head == literal => append(proof, remainingLiteral)
      case _ => None
    }
  }

  def unitList = units.foldLeft(List[SequentProof]()) { (lst,u) => (u._2)::lst }

} // class PseudoUnitsList


class PseudoUnits (minNumberOfChildren: Int)
// TODO: remove CombinedIntersection and made PseudoUnits a subclass of a class more general than AbstractRPILUAlgorithm
extends AbstractRPILUAlgorithm with LeftHeuristicC with CombinedIntersection {
  def collectUnits(iterator: ProofNodeCollection[SequentProof]) = {
    val units   = new PseudoUnitsList()
    val unitMap = MMap[SequentProof, LList[(Either[E,E],SequentProof)]]()
    iterator.foldRight(Unit) { (p,_) =>
      val children = iterator.childrenOf.getOrElse(p, Nil)
      if (fakeSize(children) >= minNumberOfChildren) {
        units.addIfPseudoUnit(p, children) match {
          case Some(l) => unitMap.update(p, l)
          case _ => Unit
        }
      }
      Unit
    }
    (units, unitMap)
  }

  def fixProofAndUnits(iterator: ProofNodeCollection[SequentProof],
                       edgesToDelete: MMap[SequentProof,DeletedSide],
                       unitMap: Map[SequentProof,LList[(Either[E,E],SequentProof)]]) = {
    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      if (unitMap contains oldProof) {
        unitMap(oldProof).elem = (unitMap(oldProof).elem._1, newProof)
        deleteFromChildren(oldProof, iterator, edgesToDelete)
      }
      newProof
    }
    iterator.foldDown(reconstructProof _)
  }

  def apply(proof: SequentProof) = {
    val iterator = ProofNodeCollection(proof)
    val (units, unitMap) = collectUnits(iterator)
    val pseudoRoot = fixProofAndUnits(iterator, MMap[SequentProof,DeletedSide](), unitMap)
//    println("root " + pseudoRoot.conclusion)
//    println("units " + units.unitList.map(_.conclusion))
    units.unitList.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}

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
