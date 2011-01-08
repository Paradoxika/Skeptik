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
  def regularizeWithOnlyRootDuplication(p: Proof) = if (p.isInstanceOf[Resolvent]) {
    doRegularize(p.asInstanceOf[Resolvent], Nil, fullyRegularizeContinuation(doNotFilterCriticalLiterals, duplicateOnlyRootAndRegularizeDuplicates))
  }
  def regularize = p => regularizeWithOnlyRootDuplication(p)

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
}
