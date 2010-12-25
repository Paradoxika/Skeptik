/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import proofCompression.Utilities._
import scala.collection.mutable._
import scala.collection._

object ProofRegularization {
  val deletedSubProof = Input(immutable.HashSet(L("Deleted SubProof",true)))

  // Very inneficient way of removing unused resolvents
  def removeUnusedResolvents(proof: ResolutionProof) = proof.duplicate

  def getIrregularNodes(proof: ResolutionProof) = {
    def getIrregularNodesRec(p: ResolutionProof, pivotsBelow: List[Atom]) : List[Int] = {
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

  def isRegular(proof: ResolutionProof) = {
    def isRegularRec(p: ResolutionProof, pivotsBelow: List[Atom]): Boolean = {
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




  def regularize(proof:ResolutionProof): Unit = {
    val regularizedProofs = new HashSet[ResolutionProof]
    def regularizeRec(p: ResolutionProof, callingChild: Resolvent, litB: Option[List[Literal]]): Unit = {

      p match {
        case Input(_) => return
        case Resolvent(left,right) => {
          if (callingChild == null) { // Root of the Proof
            doRegularize(litB.asInstanceOf[Some[List[Literal]]].get)
          }
          else {
            litB match {
              case None => p.children = p.children - callingChild   // Calling Child is orphan of the called Parent
              case Some(literalsB) => p.literalsBelow += (callingChild -> literalsB)
            }

            def hasReceivedAllCalls = {
              p.children.forall(c => p.literalsBelow.contains(c))
            }
            if (hasReceivedAllCalls) {
              val lBPerChild = (for (child <- p.children) yield p.literalsBelow(child)).toList
              val intersection = intersect(lBPerChild)
              val union = unite(lBPerChild)
              val criticalLiterals = union.diff(intersection)
              val problematicLiterals = criticalLiterals.filter(l => p.pivotAtomsAbove.contains(l.atom))
              val r = p.asInstanceOf[Resolvent]
              if (problematicLiterals.length != 0) duplicateAndRegularize
              else doRegularize(union)
            }
          }
          def duplicateAndRegularize = {
            for (c <- p.children.tail) {
              val newProof = p.duplicate
              newProof.children = c::Nil
              if (c.left == p) c.left = newProof
              else c.right = newProof
              p.children = p.children - c
              val literalsBelowForNewProof = p.literalsBelow(c)
              p.literalsBelow -= c
              regularizeRec(newProof, c, Some(literalsBelowForNewProof))
            }
            doRegularize(p.literalsBelow(p.children.head))
          }

          def doRegularize(literalsBelow: List[Literal]) = {
            try require(!regularizedProofs.contains(p))
            catch {case _ => println("id" + p.id + " ; " + p.children.map(c => c.id) + " " + regularizedProofs.map(n => n.id) + regularizedProofs.map(n => n.equals(p)) + regularizedProofs.contains(p)); throw new Exception("scheiße")}
            val r = p.asInstanceOf[Resolvent]
            if (!literalsBelow.contains(r.pivot._1) && !literalsBelow.contains(r.pivot._2)) {
              regularizeRec(left, r, Some(r.pivot._2::literalsBelow))
              regularizeRec(right, r, Some(r.pivot._1::literalsBelow))

            }
            else if (literalsBelow.contains(r.pivot._1)) {
              regularizeRec(left, r, None)
              r.left = deletedSubProof
              regularizeRec(right, r, Some(literalsBelow))
            }
            else {
              regularizeRec(right, r, None)
              r.right = deletedSubProof
              regularizeRec(left, r, Some(literalsBelow))
            }
            regularizedProofs += p
          }
        }
      }
    }
    regularizeRec(proof, null, Some(Nil))
  }


  def recyclePivot(proof:ResolutionProof): Unit = {  
    if (proof.isInstanceOf[Resolvent]) {
      val n = proof.asInstanceOf[Resolvent]
      if (allChildrenAreVisited(proof)) {
        if (proof.children.length > 1) {
          n.left.literalsBelow += (n -> Nil)
          n.right.literalsBelow += (n -> Nil)
        }
        else if (proof.children.length == 0) {
          n.left.literalsBelow += (n -> (n.pivot._2::Nil))
          n.right.literalsBelow += (n -> (n.pivot._1::Nil))
        }
        else {
          val literalsBelow = n.literalsBelow.get(n.children.head) match {case Some(set) => set; case None => throw new Exception("Literals Below was not initialized properly") }
          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
            n.left.literalsBelow += (n -> (n.pivot._2::literalsBelow ))
            n.right.literalsBelow += (n -> (n.pivot._1::literalsBelow))
          }
          else if (literalsBelow.contains(n.pivot._1)) {
            n.left.children = n.left.children - n
            n.left = deletedSubProof
            n.right.literalsBelow += (n -> literalsBelow)
          }
          else { // if (literalsBelow.contains(n.pivot._2))
            n.right.children = n.right.children - n
            n.right = deletedSubProof
            n.left.literalsBelow += (n -> literalsBelow)
          }
        }
        recyclePivot(n.left)
        recyclePivot(n.right)
      }
    }
  }

    def recyclePivotImproved(proof:ResolutionProof): Unit = {
    if (proof.isInstanceOf[Resolvent]) {
      val n = proof.asInstanceOf[Resolvent]
      if (allChildrenAreVisited(proof)) {
        if (proof.children.length > 1) {
          val lBPerChild = (for (child <- proof.children) yield proof.literalsBelow(child)).toList
          val intersection = intersect(lBPerChild)
          n.left.literalsBelow += (n -> intersection)
          n.right.literalsBelow += (n -> intersection)
        }
        else if (proof.children.length == 0) {
          n.left.literalsBelow += (n -> (n.pivot._2::Nil))
          n.right.literalsBelow += (n -> (n.pivot._1::Nil))
        }
        else {
          val literalsBelow = n.literalsBelow.get(n.children.head) match {case Some(set) => set; case None => throw new Exception("Literals Below was not initialized properly") }
          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
            n.left.literalsBelow += (n -> (n.pivot._2::literalsBelow ))
            n.right.literalsBelow += (n -> (n.pivot._1::literalsBelow))
          }
          else if (literalsBelow.contains(n.pivot._1)) {
            n.left.children = n.left.children - n
            n.left = deletedSubProof
            n.right.literalsBelow += (n -> literalsBelow)
          }
          else { // if (literalsBelow.contains(n.pivot._2))
            n.right.children = n.right.children - n
            n.right = deletedSubProof
            n.left.literalsBelow += (n -> literalsBelow)
          }
        }
        recyclePivotImproved(n.left)
        recyclePivotImproved(n.right)
      }
    }
  }

  def fixProof(proof:ResolutionProof) = fixProofRec(proof, new HashSet[ResolutionProof])
  private def fixProofRec(proof:ResolutionProof, visitedProofs: HashSet[ResolutionProof]) : Unit = {
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
            val survivingParent : ResolutionProof =
            if (n.left == deletedSubProof) n.right
            else if (n.right == deletedSubProof) n.left
            else if (n.left.clause.contains(n.pivot._1) && !n.right.clause.contains(n.pivot._2)) n.right
            else if (!n.left.clause.contains(n.pivot._1) && n.right.clause.contains(n.pivot._2)) n.left
            else {
              if (proofLength(n.left) < proofLength(n.right)) n.left
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

  def allChildrenAreVisited(proof:ResolutionProof): Boolean = {
    proof.children.length == proof.literalsBelow.size 
  }
}
