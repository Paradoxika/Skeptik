package skeptik.algorithm.compressor
package combinedRPILU

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

abstract class IrregularUnits
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection with LeftHeuristic {

  def lowerInsteadOfRegularize(proof: SequentProof, notDeletedChildren: Int):Boolean

  private def collect(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val units = scala.collection.mutable.Queue[SequentProof]()

    def isUnitAndSomething(something: (SequentProof, Int) => Boolean)
                          (p: SequentProof) =
      (fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc) == 1) && {
        val aliveChildren = nodeCollection.childrenOf.getOrElse(p,Nil).foldLeft(0) { (acc,child) =>
          if (childIsMarkedToDeleteParent(child, p, edgesToDelete)) acc else (acc + 1)
        }
        (aliveChildren > 1) && (something(p, aliveChildren))
      }
    val isUnitToLower = isUnitAndSomething(lowerInsteadOfRegularize _) _
    val isTrueUnit = isUnitAndSomething { (_,_) => true } _


    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      val (safeL,safeR) = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
      def regularize(position: DeletedSide) = 
        if (isUnitToLower(p)) lower() else {
          edgesToDelete.update(p, position)
          (p, safeL, safeR)
        }
      def lower() = {
        units.enqueue(p)
        deleteFromChildren(p, nodeCollection, edgesToDelete)
        if (fakeSize(p.conclusion.ant) == 1)
          (p, Set(p.conclusion.ant(0)), Set[E]())
        else
          (p, Set[E](), Set(p.conclusion.suc(0)))
      }
      p match {
        case CutIC(_,_,_,auxR) if safeL contains auxR => regularize(LeftDS)
        case CutIC(_,_,auxL,_) if safeR contains auxL => regularize(RightDS)
        case p => if (isTrueUnit(p)) lower() else (p, safeL, safeR)
      }
    }

    nodeCollection.bottomUp(visit)
    (units,edgesToDelete)
  }

  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val (units,edgesToDelete) = collect(nodeCollection)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, nodeCollection)
      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }
}

trait AlwaysLowerIrregularUnits extends IrregularUnits {
  def lowerInsteadOfRegularize(proof: SequentProof, notDeletedChildren: Int):Boolean = true
}

trait AlwaysRegularizeIrregularUnits extends IrregularUnits {
  def lowerInsteadOfRegularize(proof: SequentProof, notDeletedChildren: Int):Boolean = {
//    println("Irregular unit " + proof.conclusion + " with " + notDeletedChildren + " children")
    false
  }
}
