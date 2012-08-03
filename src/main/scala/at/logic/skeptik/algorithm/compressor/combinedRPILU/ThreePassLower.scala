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

  private def collect(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val (rootSafeLiterals, units, unitsMap) = collectLowerables(nodeCollection)

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      def safeLiteralsFromChild(v:(SequentProof, IClause)) = v match {
        case (p, safeLiterals) if edgesToDelete contains p => safeLiterals
        case (CutIC(left,_,_,auxR),  safeLiterals) if left  == p => safeLiterals + auxR
        case (CutIC(_,right,auxL,_), safeLiterals) if right == p => auxL +: safeLiterals
        case _ => throw new Exception("Unknown or impossible inference rule")
      }

      // Node is lowerable
      if (unitsMap contains p) {
        deleteFromChildren(p, nodeCollection, edgesToDelete)
        val (efficientLiteral, safeLiterals) = unitsMap(p)
//        println("Unit " + p.conclusion + " " + unitsMap(p))
        (p, safeLiterals)
      }

      // Root node
      else if (childrensSafeLiterals == Nil) (p, rootSafeLiterals)

      else {
        val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
        p match {
            case CutIC(_,_,_,auxR) if safeLiterals.ant contains auxR => edgesToDelete.update(p, LeftDS)
            case CutIC(_,_,auxL,_) if safeLiterals.suc contains auxL => edgesToDelete.update(p, RightDS)
            case _ =>
        }
        (p, safeLiterals)
      }
    }

    nodeCollection.bottomUp(visit)

//    for ((k,v) <- edgesToDelete) { v match {
//      case LeftDS  => println(k.conclusion + " -> " + k.premises(0).conclusion)
//      case RightDS => println(k.conclusion + " -> " + k.premises(1).conclusion)
//    }}

    // Move what's below to its own function

    // /data/proofs/QG-classification/qg5/iso_brn045.smt2 /data/proofs/QG-classification/qg5/iso_brn043.smt2 /data/proofs/QG-classification/qg5/iso_icl464.smt2 /data/proofs/QG-classification/qg5/iso_brn1187.smt2 /data/proofs/QG-classification/qg5/iso_brn1113.smt2 /data/proofs/QG-classification/qg5/iso_icl315.smt2 /data/proofs/QG-classification/qg5/iso_icl483.smt2

    val protectedLiteralsFor = MMap[SequentProof,IClause]()
    def addProtectedLiteralTo(proof: SequentProof, literals: IClause) =
      protectedLiteralsFor(proof) = protectedLiteralsFor.get(proof) match {
        case Some(clause) => clause ++ literals
        case None => literals
      }

    def dispatchProtectedLiterals(left: SequentProof, right: SequentProof, protectedLiterals: IClause, pivot: E) = {
//      println("Dispatch " + protectedLiterals + " on " + left.conclusion + " and " + right.conclusion + " pivot " + pivot)
      def eitherToClause(e: Either[E,E]) = e match {
        case Right(l) => new IClause(Set(l),Set())
        case Left(l)  => new IClause(Set(),Set(l))
      }
      def dispatch(big: SequentProof, small: SequentProof, e: Either[E,E]) = {
        val bigClause = protectedLiterals intersect IClause(big.conclusion)
        addProtectedLiteralTo(big,  bigClause ++ eitherToClause(e))
        addProtectedLiteralTo(small, (protectedLiterals -- bigClause) ++ eitherToClause(e.swap))
      }
      (left.isInstanceOf[Axiom], right.isInstanceOf[Axiom]) match {
        case (true,  false) => dispatch(left, right, Left(pivot))
        case (false, true)  => dispatch(right, left, Right(pivot))
        case (false, false)  => println("yop") ; dispatch(right, left, Right(pivot)) // Test
//        case (false, false) => dispatch(left, right, Left(pivot)) // arbitrary
        case (true,  true)  =>
      }
    }

    def keepProtectedLiterals(node: SequentProof):Unit = node match {

      case CutIC(left, right, pivot,_) =>
        var protectedLiterals = protectedLiteralsFor.getOrElse(node, IClause()) ; protectedLiteralsFor.remove(node)
        if (unitsMap contains node) {
          protectedLiterals = protectedLiterals ++ unitsMap(node)._1
//          println("Unit " + node.conclusion + " protected " + protectedLiterals)
        }
//        else if (!protectedLiterals.isFalse) println("Node " + node.conclusion + " protected " + protectedLiterals)

        if (protectedLiterals.isFalse) return
        if (!(protectedLiterals subsume IClause(node.conclusion)))
          throw new Exception("Protected literals " + protectedLiterals + " missing in " + node.conclusion)

        edgesToDelete.get(node) match {

          case Some(LeftDS) =>
            if (protectedLiterals subsume IClause(right.conclusion))
              addProtectedLiteralTo(right, protectedLiterals)
            else {
              println("L " + node.conclusion + " -> " + left.conclusion + " because " + (protectedLiterals intersect IClause(left.conclusion)))
              edgesToDelete.remove(node)
              if (protectedLiterals subsume IClause(left.conclusion)) {
                addProtectedLiteralTo(left,  protectedLiterals)
                addProtectedLiteralTo(right, new IClause(Set(pivot),Set()))
              }
              else
              dispatchProtectedLiterals(left, right, protectedLiterals, pivot)
            }

          case Some(RightDS) =>
            if (protectedLiterals subsume IClause(left.conclusion))
              addProtectedLiteralTo(left, protectedLiterals)
            else {
              println("R " + node.conclusion + " -> " + right.conclusion + " because " + (protectedLiterals intersect IClause(right.conclusion)))
              edgesToDelete.remove(node)
              if (protectedLiterals subsume IClause(right.conclusion)) {
                addProtectedLiteralTo(right, protectedLiterals)
                addProtectedLiteralTo(left, new IClause(Set(),Set(pivot)))
              }
              else
              dispatchProtectedLiterals(left, right, protectedLiterals, pivot)
            }

          case None =>
            if (protectedLiterals subsume IClause(left.conclusion)) {
              addProtectedLiteralTo(left,  protectedLiterals)
              addProtectedLiteralTo(right, new IClause(Set(pivot),Set()))
            }
            else
            if (protectedLiterals subsume IClause(right.conclusion)) {
              addProtectedLiteralTo(right, protectedLiterals)
              addProtectedLiteralTo(left, new IClause(Set(),Set(pivot)))
            }
            else
            dispatchProtectedLiterals(left, right, protectedLiterals, pivot)
        }

      case _ => protectedLiteralsFor.remove(node)
            
    }
    
    nodeCollection.foreach(keepProtectedLiterals)

//    for ((k,v) <- edgesToDelete) { v match {
//      case LeftDS  => println(k.conclusion + " -> " + k.premises(0).conclusion)
//      case RightDS => println(k.conclusion + " -> " + k.premises(1).conclusion)
//    }}

    (units, edgesToDelete)
  }



  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val (units, edgesToDelete) = collect(nodeCollection)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, nodeCollection)
      for (k <- units) {
        val v = fixMap(k)
        if (k.conclusion == v.conclusion)
          println("I " + k.conclusion)
        else
          println("C " + k.conclusion + " -> " + v.conclusion)
      }
      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }
}

class ThreePassLower
extends AbstractThreePassLower {
  protected def collectLowerables(nodeCollection: ProofNodeCollection[SequentProof]) = {
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
