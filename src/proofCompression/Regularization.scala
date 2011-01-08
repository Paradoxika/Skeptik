/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import proofCompression.Utilities._
import scala.collection.mutable._
import scala.collection._

object Regularization {
  val deletedSubProof = Input(immutable.HashSet(L("Deleted SubProof",true)))

  // Very inneficient way of removing unused resolvents
  def removeUnusedResolvents(proof: Proof) = proof.duplicate

  def getIrregularNodes(proof: Proof) = {
    def getIrregularNodesRec(p: Proof, pivotsBelow: List[Atom]) : List[Int] = {
      p match {
        case Input(_) => Nil
        case Resolvent(l,r) => {
          if (p.asInstanceOf[Resolvent].pivot._1.atom == "v115") println(p.id)
          val pivotsBelowNext = p.asInstanceOf[Resolvent].pivot._1.atom::pivotsBelow
          val listL = getIrregularNodesRec(l,pivotsBelowNext)
          val listR = getIrregularNodesRec(r,pivotsBelowNext)
          if (pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) {
            println(p.id + " (" + p.asInstanceOf[Resolvent].left.id + "," + p.asInstanceOf[Resolvent].right.id + ") " + p.asInstanceOf[Resolvent].pivot + " : " + pivotsBelow)
            return p.id::(listL:::listR)
          }
          else return listL:::listR
        }
      }
    }
    getIrregularNodesRec(proof, Nil)
  }

  def isRegular(proof: Proof) = {
    def isRegularRec(p: Proof, pivotsBelow: List[Atom]): Boolean = {
      p match {
        case Input(_) => true
        case Resolvent(l, r) => {
          if (pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom)) println("Non-regular atom: " + p.asInstanceOf[Resolvent].pivot._1.atom + " ; id: " + p.id + " ; number of children: " + p.children.length)
          val pivotsBelowNext = p.asInstanceOf[Resolvent].pivot._1.atom::pivotsBelow
          !pivotsBelow.contains(p.asInstanceOf[Resolvent].pivot._1.atom) &&
          isRegularRec(l, pivotsBelowNext) &&
          isRegularRec(r, pivotsBelowNext)
        }
      }
    }
    isRegularRec(proof, Nil)
  }



  def doRegularize(p: Resolvent, criticalLiterals: List[Literal], continuation: Resolvent => Unit) = {
    if (!criticalLiterals.contains(p.pivot._1) && !criticalLiterals.contains(p.pivot._2)) {
      regularizationRecSchema(p.left, p, Some(p.pivot._2::criticalLiterals), continuation)
      regularizationRecSchema(p.right, p, Some(p.pivot._1::criticalLiterals), continuation)
    }
    else if (criticalLiterals.contains(p.pivot._1)) {
      regularizationRecSchema(p.left, p, None, continuation)
      p.left = deletedSubProof
      regularizationRecSchema(p.right, p, Some(criticalLiterals), continuation)
    }
    else {
      regularizationRecSchema(p.right, p, None, continuation)
      p.right = deletedSubProof
      regularizationRecSchema(p.left, p, Some(criticalLiterals), continuation)
    }
  }

  def regularizationRecSchema(p: Proof, callingChild: Resolvent, litB: Option[List[Literal]], continuation: Resolvent => Unit): Unit = {
    p match {
      case Input(_) => return
      case Resolvent(left,right) => {
        val r = p.asInstanceOf[Resolvent]
        litB match {
          case None => p.children = p.children - callingChild   // Calling Child is orphan of the called Parent
          case Some(literalsB) => p.literalsBelow += (callingChild -> literalsB)
        }
        def hasReceivedAllCalls = p.children.forall(c => p.literalsBelow.contains(c))
        if (hasReceivedAllCalls) continuation(r)
      }
    }
  }

  


  def recyclePivots(p:Proof) = if (p.isInstanceOf[Resolvent]) doRegularize(p.asInstanceOf[Resolvent], Nil, recyclePivotsContinuation)
  def recyclePivotsContinuation: Resolvent => Unit = r => {
    val criticalLiterals = if (r.children.length == 1) r.literalsBelow(r.children.head) // case where r has only one child
                           else Nil                                                     // case where r has zero or many children
    doRegularize(r, criticalLiterals, recyclePivotsContinuation)
  }


  def recyclePivotsWithIntersection(p:Proof) = if (p.isInstanceOf[Resolvent]) doRegularize(p.asInstanceOf[Resolvent], Nil, recyclePivotsWithIntersectionContinuation)
  def recyclePivotsWithIntersectionContinuation: Resolvent => Unit = r => {
    val criticalLiterals = if (r.children.length == 1) r.literalsBelow(r.children.head) // case where r has only one child
                           else if (r.children.length > 1) {                            // case where r has many children
                             val lBPerChild = (for (child <- r.children) yield r.literalsBelow(child)).toList
                             intersect(lBPerChild)
                           }
                           else Nil // case where r has zero children
    doRegularize(r, criticalLiterals, recyclePivotsWithIntersectionContinuation)
  }
  
  def fullyRegularizeContinuation(filterCriticalLiterals: List[Literal] => List[Literal], duplicateAndRegularizeDuplicates: (List[Literal] => List[Literal]) => Resolvent => List[Literal] => Unit): Resolvent => Unit = r => {
    val lBPerChild = (for (child <- r.children) yield r.literalsBelow(child)).toList
    val intersection = intersect(lBPerChild)
    val union = unite(lBPerChild)
    val criticalLiterals = filterCriticalLiterals(union.diff(intersection))
    if (criticalLiterals.length != 0) duplicateAndRegularizeDuplicates(filterCriticalLiterals)(r)(criticalLiterals)
    else doRegularize(r, intersection, fullyRegularizeContinuation(filterCriticalLiterals, duplicateAndRegularizeDuplicates))
  }

  
  def regularizeNaive(p: Proof) = if (p.isInstanceOf[Resolvent]) {
    doRegularize(p.asInstanceOf[Resolvent], Nil, fullyRegularizeContinuation(doNotFilterCriticalLiterals, simpleDuplicateAndRegularizeDuplicates))
  }
  def regularizeOnlyRootDuplication(p: Proof) = if (p.isInstanceOf[Resolvent]) {
    doRegularize(p.asInstanceOf[Resolvent], Nil, fullyRegularizeContinuation(doNotFilterCriticalLiterals, duplicateOnlyRootAndRegularizeDuplicates))
  }


  def doNotFilterCriticalLiterals(criticalLiterals: List[Literal]) = criticalLiterals
  def simpleDuplicateAndRegularizeDuplicates(filterCriticalLiterals: List[Literal] => List[Literal])(r: Resolvent)(criticalLiterals: List[Literal]):Unit = {
    for (c <- r.children.tail) {
      val newProof = r.duplicate
      newProof.children = c::Nil
      if (c.left == r) c.left = newProof
      else c.right = newProof
      r.children = r.children - c
      val literalsBelowForNewProof = r.literalsBelow(c)
      r.literalsBelow -= c
      regularizationRecSchema(newProof, c, Some(literalsBelowForNewProof), fullyRegularizeContinuation(filterCriticalLiterals, simpleDuplicateAndRegularizeDuplicates))
    }
    doRegularize(r, r.literalsBelow(r.children.head), fullyRegularizeContinuation(filterCriticalLiterals, simpleDuplicateAndRegularizeDuplicates))
  }
  def duplicateOnlyRootAndRegularizeDuplicates(filterCriticalLiterals: List[Literal] => List[Literal])(r: Resolvent)(criticalLiterals: List[Literal]):Unit = {
    for (c <- r.children.tail) {
      val newProof = r.duplicateRoot
      newProof.children = c::Nil
      if (c.left == r) c.left = newProof
      else c.right = newProof
      r.children = r.children - c
      val literalsBelowForNewProof = r.literalsBelow(c)
      r.literalsBelow -= c
      regularizationRecSchema(newProof, c, Some(literalsBelowForNewProof), fullyRegularizeContinuation(filterCriticalLiterals, duplicateOnlyRootAndRegularizeDuplicates))
    }
    doRegularize(r, r.literalsBelow(r.children.head), fullyRegularizeContinuation(filterCriticalLiterals, duplicateOnlyRootAndRegularizeDuplicates))
  }

  def fixProof(proof:Proof) = fixProofRec(proof, new HashSet[Proof])
  private def fixProofRec(proof:Proof, visitedProofs: HashSet[Proof]) : Unit = {
    if (!visitedProofs.contains(proof)) {
      visitedProofs += proof
      proof match {
        case Input(c) => return
        case n : Resolvent => {
          fixProofRec(n.left, visitedProofs)
          fixProofRec(n.right, visitedProofs)
          if (n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) {
            n.update
          }
          else {
            val survivingParent : Proof =
              if (n.left == deletedSubProof) n.right
              else if (n.right == deletedSubProof) n.left
              else if (n.left.clause.contains(n.pivot._1) && !n.right.clause.contains(n.pivot._2)) n.right
              else if (!n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) n.left
              else {
                if (n.left.length < n.right.length) n.left
                else n.right
              }

            n.left.children -= n
            n.right.children -= n
            for (child <- n.children) {
              if (child.left == n) child.left = survivingParent
              else child.right = survivingParent
              survivingParent.children = child::survivingParent.children
            }
          }
        }
      }
    }
  }

//  def recyclePivotsOld(proof:Proof): Unit = {
//    if (proof.isInstanceOf[Resolvent]) {
//      val n = proof.asInstanceOf[Resolvent]
//      println(n.id + " : " + n.children.length + " : " + allChildrenAreVisited(proof))
//      if (allChildrenAreVisited(proof)) {
//        if (proof.children.length > 1) {
//          n.left.literalsBelow += (n -> Nil)
//          n.right.literalsBelow += (n -> Nil)
//        }
//        else if (proof.children.length == 0) {
//          n.left.literalsBelow += (n -> (n.pivot._2::Nil))
//          n.right.literalsBelow += (n -> (n.pivot._1::Nil))
//        }
//        else {
//          val literalsBelow = n.literalsBelow(n.children.head)
//          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
//            n.left.literalsBelow += (n -> (n.pivot._2::literalsBelow ))
//            n.right.literalsBelow += (n -> (n.pivot._1::literalsBelow))
//          }
//          else if (literalsBelow.contains(n.pivot._1)) {
//            n.left.children = n.left.children - n
//            n.left = deletedSubProof
//            n.right.literalsBelow += (n -> literalsBelow)
//          }
//          else { // if (literalsBelow.contains(n.pivot._2))
//            n.right.children = n.right.children - n
//            n.right = deletedSubProof
//            n.left.literalsBelow += (n -> literalsBelow)
//          }
//        }
//        recyclePivots(n.left)
//        recyclePivots(n.right)
//      }
//    }
//  }
//
//    def recyclePivotsWithIntersectionOld(proof:Proof): Unit = {
//    if (proof.isInstanceOf[Resolvent]) {
//      val n = proof.asInstanceOf[Resolvent]
//      if (allChildrenAreVisited(proof)) {
//        if (proof.children.length > 1) {
//          val lBPerChild = (for (child <- proof.children) yield proof.literalsBelow(child)).toList
//          val intersection = intersect(lBPerChild)
//          n.left.literalsBelow += (n -> intersection)
//          n.right.literalsBelow += (n -> intersection)
//        }
//        else if (proof.children.length == 0) {
//          n.left.literalsBelow += (n -> (n.pivot._2::Nil))
//          n.right.literalsBelow += (n -> (n.pivot._1::Nil))
//        }
//        else {
//          val literalsBelow = n.literalsBelow.get(n.children.head) match {case Some(set) => set; case None => throw new Exception("Literals Below was not initialized properly") }
//          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
//            n.left.literalsBelow += (n -> (n.pivot._2::literalsBelow ))
//            n.right.literalsBelow += (n -> (n.pivot._1::literalsBelow))
//          }
//          else if (literalsBelow.contains(n.pivot._1)) {
//            n.left.children = n.left.children - n
//            n.left = deletedSubProof
//            n.right.literalsBelow += (n -> literalsBelow)
//          }
//          else { // if (literalsBelow.contains(n.pivot._2))
//            n.right.children = n.right.children - n
//            n.right = deletedSubProof
//            n.left.literalsBelow += (n -> literalsBelow)
//          }
//        }
//        recyclePivotsWithIntersection(n.left)
//        recyclePivotsWithIntersection(n.right)
//      }
//    }
//  }



//  def allChildrenAreVisited(proof:Proof): Boolean = {
//    proof.children.length == proof.literalsBelow.size
//  }
}
