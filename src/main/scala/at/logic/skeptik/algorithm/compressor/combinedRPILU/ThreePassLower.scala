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
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection {

  /** Collect nodes to be lowered
   *
   * This is the fist pass of the algorithm.
   *
   * Nodes collected by this function should have at most one pivot candidate
   * when reintroduced.
   *
   * @return The lowered literals clause, the ordered sequence of lowered
   * nodes, a map from lowered node to its efficient literal and the safe
   * literals.
   */
  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]):(IClause, Seq[SequentProof], Map[SequentProof,(IClause,IClause)])

  protected def addProtectedLiterals(literals: IClause, node: SequentProof, protectedLiteralMap: MMap[SequentProof,IClause]) =
    if (!literals.isFalse)
      protectedLiteralMap.update(node, if (protectedLiteralMap contains node) protectedLiteralMap(node) ++ literals else literals)

  protected def computeEdgesToDeleteAndProtectedLiterals(node: SequentProof,
                                                         safeLiterals: IClause, edgesToDelete: MMap[SequentProof,DeletedSide],
                                                         protectedLiteralMap: MMap[SequentProof,IClause]):Unit = {
    val protectedLiterals = protectedLiteralMap.getOrElse(node, IClause()) ; protectedLiteralMap.remove(node)
    lazy val leftLiterals  = IClause(node.premises.head.conclusion)
    lazy val rightLiterals = IClause(node.premises.last.conclusion)
    node match {

      case CutIC(_,right,_,auxR) if (safeLiterals.ant contains auxR) && (protectedLiterals -- rightLiterals).isFalse =>
        edgesToDelete.update(node, LeftDS)
        addProtectedLiterals(protectedLiterals, right, protectedLiteralMap)
      case CutIC(left ,_,auxL,_) if (safeLiterals.suc contains auxL) && (protectedLiterals --  leftLiterals).isFalse =>
        edgesToDelete.update(node, RightDS)
        addProtectedLiterals(protectedLiterals, left, protectedLiteralMap)

      case CutIC(left,right,pivot,_) =>
        if (protectedLiterals.isFalse) return
        val remainingProtectedLiterals =
          (protectedLiterals -- protectedLiteralMap.getOrElse(left, IClause())) -- protectedLiteralMap.getOrElse(right, IClause())
        if (remainingProtectedLiterals.isFalse) return
        if (left.isInstanceOf[Axiom] || (remainingProtectedLiterals subsume leftLiterals)) {
          var protectedLeft  = remainingProtectedLiterals intersect leftLiterals
          var protectedRight = remainingProtectedLiterals    --     leftLiterals
          if (!protectedLeft.isFalse)  protectedRight = pivot +: protectedRight
          if (!protectedRight.isFalse) protectedLeft  = protectedLeft  +  pivot
          addProtectedLiterals( protectedLeft, left, protectedLiteralMap)
          addProtectedLiterals(protectedRight, right, protectedLiteralMap)
        }
        else {
          var protectedLeft  = remainingProtectedLiterals    --     rightLiterals
          var protectedRight = remainingProtectedLiterals intersect rightLiterals
          if (!protectedLeft.isFalse)  protectedRight = pivot +: protectedRight
          if (!protectedRight.isFalse) protectedLeft  = protectedLeft  +  pivot
          addProtectedLiterals( protectedLeft, left, protectedLiteralMap)
          addProtectedLiterals(protectedRight, right, protectedLiteralMap)
        }

      // Non-resolution step are ignored
      case _ =>
    }
  }

  protected def collectEdgesToDelete(nodeCollection: ProofNodeCollection[SequentProof],
                                     rootSafeLiterals: IClause,
                                     unitsMap: Map[SequentProof,(IClause,IClause)]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()

    // Protected literals transmited by children aren't the same for the both premises.
    // Hence we need to store them ourself.
    val protectedLiteralMap = MMap[SequentProof,IClause]()

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      val safeLiterals = if (unitsMap contains p) {
        deleteFromChildren(p, nodeCollection, edgesToDelete)
        val (efficientLiteral, safeLiteralsForUnit) = unitsMap(p)
        addProtectedLiterals(efficientLiteral, p, protectedLiteralMap)
//        println("Unit " + p.conclusion)
        safeLiteralsForUnit
      }
      else if (childrensSafeLiterals == Nil) rootSafeLiterals
      else computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)

      computeEdgesToDeleteAndProtectedLiterals(p, safeLiterals, edgesToDelete, protectedLiteralMap)

//      p match {
//        case CutIC(left,right,pivot,_) if (pivot.toString == "=e4ope2e1") =>
//          def unitOrNode(s: SequentProof) = if (unitsMap contains s) "Unit" else "Node"
//          println("Pivot on (" + unitOrNode(left) + ", " + unitOrNode(right) + ")")
//          edgesToDelete.get(p) match {
//            case Some(LeftDS)  => println("Deleting left")
//            case Some(RightDS) => println("Deleting right")
//            case None          => println("No deletion " + safeLiterals)
//          }
//        case _ =>
//      }

      (p, safeLiterals)
    }

    nodeCollection.bottomUp(visit)
    edgesToDelete
  }



  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)

    // First pass
    val (rootSafeLiterals, units, unitsMap) = collectLowerables(nodeCollection)
    val nbUnitChildren = units.foldLeft(0) { (acc,node) => acc + nodeCollection.childrenOf(node).length }
    println(units.length + " units with " + nbUnitChildren + " children" )

    // Second pass
    val edgesToDelete = collectEdgesToDelete(nodeCollection, rootSafeLiterals, unitsMap)
    println(edgesToDelete.size + " edges to delete (" + (edgesToDelete.size - nbUnitChildren) + " without units' children)")
//    for ((n,e) <- edgesToDelete) {
//      val premise = e match {
//        case LeftDS  => n.premises(0)
//        case RightDS => n.premises(1)
//      }
//      if (!(unitsMap contains premise)) n match {
//        case CutIC(_,_,pivot,_) => println(pivot)
//        case _ =>
//      }
//    }

    // Third pass
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, nodeCollection)
//      for (k <- units) {
//        val v = fixMap(k)
//        if (k.conclusion == v.conclusion)
//          println("I " + k.conclusion)
//        else
//          println("C " + k.conclusion + " -> " + v.conclusion)
//      }
//      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
//        try {CutIC(left,right)} catch {case e:Exception => left}
//      }
//      def firstVar(n: SequentProof) = try { n.conclusion.ant.head } catch { case _:NoSuchElementException => n.conclusion.suc.head }
      units.foldLeft(fixMap(proof)) { (root, unit) =>
//        val efficientLiteral = firstVar(unit)
//        println("R " + efficientLiteral + " in " + root.conclusion + " with " + fixMap(unit).conclusion + " was " + unit.conclusion)
        if (unit.conclusion.ant.isEmpty)
          CutIC(fixMap(unit), root, _ == unit.conclusion.suc.head, true)
        else
          CutIC(root, fixMap(unit), _ == unit.conclusion.ant.head, true)
//        CutIC(root, fixMap(unit))
      }
    }
  }
}

// /data/proofs/QG-classification/qg5/iso_icl906.smt2 /data/proofs/QG-classification/qg5/iso_brn855.smt2 /data/proofs/QG-classification/qg5/gensys_icl504.smt2

class ThreePassLower
extends AbstractThreePassLower {

  // Different from RPILU on :
  // /data/proofs/QG-classification/qg5/iso_icl464.smt2 /data/proofs/QG-classification/qg5/iso_brn397.smt2 /data/proofs/QG-classification/qg5/iso_icl751.smt2 /data/proofs/QG-classification/qg5/iso_icl048.smt2 /data/proofs/QG-classification/qg5/iso_icl487.smt2 /data/proofs/QG-classification/qg5/iso_brn1086.smt2 

  // Just remove this overriding method to have the inefficient but correct compression algorithm
  override protected def computeEdgesToDeleteAndProtectedLiterals(node: SequentProof,
                                                         safeLiterals: IClause, edgesToDelete: MMap[SequentProof,DeletedSide],
                                                         protectedLiteralMap: MMap[SequentProof,IClause]):Unit = {
    protectedLiteralMap.remove(node)
    node match {
      case CutIC(_,right,_,auxR) if (safeLiterals.ant contains auxR) =>
        edgesToDelete.update(node, LeftDS)
      case CutIC(left ,_,auxL,_) if (safeLiterals.suc contains auxL) =>
        edgesToDelete.update(node, RightDS)
      case _ =>
    }
  }

  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val map = MMap[SequentProof, (IClause,IClause)]()
    val units = scala.collection.mutable.Stack[SequentProof]()
    val rootSafeLiterals = nodeCollection.foldRight (IClause()) { (p, safeLiterals) =>
      (fakeSize(p.conclusion.ant), fakeSize(p.conclusion.suc), fakeSize(nodeCollection.childrenOf(p))) match {
        // TODO : should I add the unit's literal to safeLiterals to be transmited to unit's premises ?
        case (1,0,2) =>
          val literal = p.conclusion.ant(0)
          units.push(p)
          map.update(p, (new IClause(Set[E](literal),Set[E]()), literal +: safeLiterals))
          safeLiterals + literal
        case (0,1,2) =>
          val literal = p.conclusion.suc(0)
          units.push(p)
          map.update(p, (new IClause(Set[E](),Set[E](literal)), safeLiterals + literal))
          literal +: safeLiterals
        case _ => safeLiterals
      }
    }
    (rootSafeLiterals, units, map)
  } 
}
