package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.mutable.{SetSequent => MClause}
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

package pseudoUnits {

  abstract sealed class NodeKind
  case class  PseudoUnit (val literal: Either[E,E])  extends NodeKind
  case object DeletableNode extends NodeKind
  case object OrdinaryNode  extends NodeKind

  object isPseudoUnit
  {
    def apply(newProof: SequentProof, oldProof: SequentProof, children: List[SequentProof], principalLiterals: MClause):NodeKind = {
      val literals = literalsIntroducedByDeletion(newProof, oldProof, children, principalLiterals)
  //      println("Remaining Literals " + literals)
      (literals.ant.size, literals.suc.size) match {
        case (0,0) => DeletableNode
        case (1,0) => checkLiteralsIntroducedByLowering(newProof, Left(literals.ant.head),  principalLiterals)
        case (0,1) => checkLiteralsIntroducedByLowering(newProof, Right(literals.suc.head), principalLiterals)
        case _ => OrdinaryNode
      }
    }
    def apply(proof: SequentProof, children: List[SequentProof], principalLiterals: MClause):NodeKind =
        apply(proof, proof, children, principalLiterals)

    private def literalsIntroducedByDeletion(newProof: SequentProof, oldProof: SequentProof,
                                             children: Seq[SequentProof], principalLiterals: MClause) = {
      val result = MClause()
      children.foreach { (child) =>
          child match {
          case CutIC(left, right, aux, _) if left  == oldProof =>
//            if (!(principalLiterals.suc contains aux) && (newProof.conclusion.suc contains aux)) result += aux
//            if (!(newProof.conclusion.suc contains aux)) println(aux + " in " + oldProof.conclusion + " but not in " + newProof.conclusion)
            if (!(principalLiterals.suc contains aux)) result += aux
          case CutIC(left, right, aux, _) if right == oldProof =>
//            if (!(principalLiterals.ant contains aux) && (newProof.conclusion.ant contains aux)) aux =+: result
//            if (!(newProof.conclusion.ant contains aux)) println(aux + " in " + oldProof.conclusion + " but not in " + newProof.conclusion)
            if (!(principalLiterals.ant contains aux)) aux =+: result
          case _ =>
          }
      }
      result
    }

    private def checkLiteralsIntroducedByLowering(proof: SequentProof, remainingLiteral: Either[E,E], principalLiterals: MClause) = {
      val (leftLiterals, rightLiterals) = (proof.conclusion.ant.toSet -- principalLiterals.suc,
                                           proof.conclusion.suc.toSet -- principalLiterals.ant)
      (leftLiterals.size, rightLiterals.size, remainingLiteral) match {
        case (1,0,Left(literal))  if leftLiterals.head  == literal => literal =+: principalLiterals ; PseudoUnit(remainingLiteral)
        case (0,1,Right(literal)) if rightLiterals.head == literal => principalLiterals += literal  ; PseudoUnit(remainingLiteral)
        case _ => OrdinaryNode
      }
    }

  } // object isPseudoUnit
} // package pseudoUnits

import pseudoUnits._

trait PseudoUnitsDuringFixing
extends AbstractRPILUAlgorithm with LeftHeuristic {
  def fixProofAndLowerUnits(minNumberOfChildren: Int, nodeCollection: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) = {

    var units = List[SequentProof]()
    val principalLiterals = MClause()

    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      val children = nodeCollection.childrenOf(oldProof) filter { child => !childIsMarkedToDeleteParent(child, oldProof, edgesToDelete) }
      if (fakeSize(children) >= minNumberOfChildren) isPseudoUnit(newProof, oldProof, children, principalLiterals) match {
        case PseudoUnit(_) => units ::= newProof ; deleteFromChildren(oldProof, nodeCollection, edgesToDelete)
        case DeletableNode => deleteFromChildren(oldProof, nodeCollection, edgesToDelete)
        case _ =>
      }
      newProof
    }

    val pseudoRoot = nodeCollection.foldDown(reconstructProof _)
    units.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}

class PseudoUnits (minNumberOfChildren: Int)
extends AbstractRPILUAlgorithm with PseudoUnitsDuringFixing {
  def apply(proof: SequentProof): SequentProof =
    fixProofAndLowerUnits(minNumberOfChildren, ProofNodeCollection(proof), MMap[SequentProof,DeletedSide]())
}

class PseudoUnitsAfter (minNumberOfChildren: Int)
extends AbstractRPIAlgorithm with CollectEdgesUsingSafeLiterals with PseudoUnitsDuringFixing with Intersection {
  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(nodeCollection)
    fixProofAndLowerUnits(minNumberOfChildren, nodeCollection, edgesToDelete)
  }
}

class PseudoUnitsBefore (minNumberOfChildren: Int)
extends AbstractThreePassLower {
  def collectUnits(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val principalLiterals = MClause()
    var units = List[SequentProof]()
    val map = MMap[SequentProof, (IClause,IClause)]()
    val rootSafeLiterals = nodeCollection.foldRight (IClause()) { (p, safeLiterals) =>
      val children = nodeCollection.childrenOf(p)
      if (fakeSize(children) < minNumberOfChildren) safeLiterals else
        isPseudoUnit(p, children, principalLiterals) match {
          // TODO : should I add the unit's literal to safeLiterals to be transmited to unit's premises ?
          case PseudoUnit(Left(l))  =>
            units ::= p
            map.update(p, (new IClause(Set[E](l),Set[E]()), safeLiterals))
            safeLiterals + l
          case PseudoUnit(Right(l)) =>
            units ::= p
            map.update(p, (new IClause(Set[E](),Set[E](l)), safeLiterals))
            l +: safeLiterals
          case _ => safeLiterals
        }
    }
    (rootSafeLiterals, units, map)
  } 
}
