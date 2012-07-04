package skeptik.algorithm.compressor
package combinedRPILU

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

package pseudoUnits {

  abstract sealed class NodeKind
  case class  PseudoUnit (val literal: Either[E,E])  extends NodeKind
  case object DeletableNode extends NodeKind
  case object OrdinaryNode  extends NodeKind

  class CheckIfPseudoUnit
  {

    val literalsDeletedByUnits = (MSet[E](),MSet[E]())

    private def append(literal: Either[E,E]) = literal match {
      case Left(v)  => literalsDeletedByUnits._1.add(v)
      case Right(v) => literalsDeletedByUnits._2.add(v)
    }

    def apply(newProof: SequentProof, oldProof: SequentProof, children: List[SequentProof]):NodeKind = {
      val literals = literalsIntroducedByDeletion(newProof, oldProof, children)
  //      println("Remaining Literals " + literals)
      (literals._1.size, literals._2.size) match {
        case (0,0) => DeletableNode
        case (0,1) => checkLiteralsIntroducedByLowering(newProof, Left(literals._2.head))
        case (1,0) => checkLiteralsIntroducedByLowering(newProof, Right(literals._1.head))
        case _ => OrdinaryNode
      }
    }
    def apply(proof: SequentProof, children: List[SequentProof]):NodeKind =
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
        (literalsIntroducedByDeletion._1 -- literalsDeletedByUnits._2,
          literalsIntroducedByDeletion._2 -- literalsDeletedByUnits._1)
    }

    private def checkLiteralsIntroducedByLowering(proof: SequentProof, remainingLiteral: Either[E,E]) = {
      val (leftLiterals, rightLiterals) = (proof.conclusion.ant.toSet -- literalsDeletedByUnits._2,
                                          proof.conclusion.suc.toSet -- literalsDeletedByUnits._1)
      (leftLiterals.size, rightLiterals.size, remainingLiteral) match {
        case (1,0,Left(literal))  if leftLiterals.head  == literal => append(remainingLiteral) ; PseudoUnit(remainingLiteral)
        case (0,1,Right(literal)) if rightLiterals.head == literal => append(remainingLiteral) ; PseudoUnit(remainingLiteral)
        case _ => OrdinaryNode
      }
    }

  } // class CheckIfPseudoUnit
} // object pseudoUnits

import pseudoUnits._

trait PseudoUnitsNotDuringFixing
extends AbstractRPILUAlgorithm with LeftHeuristic {
  def fixProofAndUnits(nodeCollection: ProofNodeCollection[SequentProof],
                       edgesToDelete: MMap[SequentProof,DeletedSide],
                       unitMap: Map[SequentProof,LList[SequentProof]]) = {
    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      if (unitMap contains oldProof) {
        unitMap(oldProof).elem = newProof
        deleteFromChildren(oldProof, nodeCollection, edgesToDelete)
      }
      newProof
    }
    nodeCollection.foldDown(reconstructProof _)
  }
}

class PseudoUnits (minNumberOfChildren: Int)
extends AbstractRPILUAlgorithm with PseudoUnitsNotDuringFixing {
  def collectUnits(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val isPseudoUnit = new CheckIfPseudoUnit()
    var units   = LList[SequentProof]()
    val unitMap = MMap[SequentProof, LList[SequentProof]]()
    nodeCollection.foreachDown { (p) =>
      val children = nodeCollection.childrenOf(p)
      if (fakeSize(children) >= minNumberOfChildren) {
        isPseudoUnit(p, children) match {
          case PseudoUnit(_) =>
            units = new LList(p, units)
            unitMap.update(p, units)
          case _ =>
        }
      }
    }
    (units, unitMap)
  }

  def apply(proof: SequentProof) = {
    val nodeCollection = ProofNodeCollection(proof)
    val (units, unitMap) = collectUnits(nodeCollection)
    val pseudoRoot = fixProofAndUnits(nodeCollection, MMap[SequentProof,DeletedSide](), unitMap)
//    println("root " + pseudoRoot.conclusion)
//    println("units " + units.map(_.conclusion))
    units.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}

trait PseudoUnitsDuringFixing
extends AbstractRPILUAlgorithm with LeftHeuristic {
  def fixProofAndLowerUnits(minNumberOfChildren: Int, nodeCollection: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) = {

    var units = List[SequentProof]()
    val isPseudoUnit = new CheckIfPseudoUnit()

    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
      val children = nodeCollection.childrenOf(oldProof) filter { child => !childIsMarkedToDeleteParent(child, oldProof, edgesToDelete) }
      if (fakeSize(children) >= minNumberOfChildren) isPseudoUnit(newProof, oldProof, children) match {
        case PseudoUnit(_) => units ::= newProof ; deleteFromChildren(oldProof, nodeCollection, edgesToDelete)
        case DeletableNode => deleteFromChildren(oldProof, nodeCollection, edgesToDelete)
        case _ =>
      }
      newProof
    }

    val pseudoRoot = nodeCollection.foldDown(reconstructProof _)
//    println("root " + pseudoRoot.conclusion)
//    println("units " + units.map(_.conclusion))
    units.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}

class OnePassPseudoUnits (minNumberOfChildren: Int)
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
    val isPseudoUnit = new CheckIfPseudoUnit()
    var units = List[SequentProof]()
    val map = MMap[SequentProof, (Set[E],Set[E])]()
    val rootSafeLiterals = nodeCollection.foldRight ((Set[E](), Set[E]())) { (p, set) =>
      val children = nodeCollection.childrenOf(p)
      if (fakeSize(children) < minNumberOfChildren) set else
        isPseudoUnit(p, children) match {
          case PseudoUnit(Left(l))  => units ::= p ; map.update(p,set) ; (set._1, set._2 + l)
          case PseudoUnit(Right(l)) => units ::= p ; map.update(p,set) ; (set._1 + l, set._2)
          case _ => set
        }
    }
    (rootSafeLiterals, units, map)
  } 
}
