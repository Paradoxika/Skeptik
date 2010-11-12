/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import proofCompression.ResolutionCalculus._
import proofCompression.Utilities._
import scala.collection.mutable._

object ProofRegularization {
  val deletedSubProof = Input(L("DELETED",true)::Nil)


  def regularize(proof:ResolutionProof): Unit = {
    if (proof.isInstanceOf[Resolvent]) {
      val n = proof.asInstanceOf[Resolvent]
      if (allChildrenAreVisited(proof)) {
        if (proof.children.length > 1) {
          val literalsBelow = (for (child <- proof.children) yield proof.literalsBelow(child)).toList
          val intersectionOfLiteralsBelow = intersection(literalsBelow)
          val problematicLiterals = union(literalsBelow).diff(intersectionOfLiteralsBelow)

          if (problematicLiterals.isEmpty) {
            n.left.literalsBelow += (n -> intersectionOfLiteralsBelow)
            n.right.literalsBelow += (n -> intersectionOfLiteralsBelow)
            regularize(n.left)
            regularize(n.right)
          }
          else {
            def findProblematicLiteralsAbove(literals: HashSet[Literal], p: ResolutionProof, visitedProofs: HashSet[ResolutionProof]): Boolean = {
              if (!visitedProofs.contains(p)) {
                visitedProofs += p
                p match {
                  case Input(c) => return false
                  case Resolvent(l,r) => {
                    if (literals.contains(p.asInstanceOf[Resolvent].pivot._1) || literals.contains(p.asInstanceOf[Resolvent].pivot._2)) return true
                    else return (findProblematicLiteralsAbove(literals, l, visitedProofs) || findProblematicLiteralsAbove(literals, r, visitedProofs))
                  }
                }
              } else return false
            }
            if (findProblematicLiteralsAbove(problematicLiterals, n, new HashSet[ResolutionProof])) {
              for (child <- n.children) {
                val newProof = n.duplicate.asInstanceOf[Resolvent]
                newProof.children = child::Nil
                newProof.literalsBelow += (child -> n.literalsBelow(child))
                if (child.left == proof) child.left = newProof
                else child.right = newProof
                regularize(newProof)
              }
            }
            else {
              n.left.literalsBelow += (n -> intersectionOfLiteralsBelow)
              n.right.literalsBelow += (n -> intersectionOfLiteralsBelow)
              regularize(n.left)
              regularize(n.right)
            }
          }
          
        }
        else if (proof.children.length == 0) {
          n.left.literalsBelow += (n -> (new HashSet[Literal] + n.pivot._2))
          n.right.literalsBelow += (n -> (new HashSet[Literal] + n.pivot._1))
          regularize(n.left)
          regularize(n.right)
        }
        else {
          val literalsBelow = n.literalsBelow.get(n.children.head) match {case Some(set) => set; case None => throw new Exception("Literals Below was not initialized properly") }
          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
            n.left.literalsBelow += (n -> (literalsBelow.clone + n.pivot._2))
            n.right.literalsBelow += (n -> (literalsBelow.clone + n.pivot._1))
          }
          else if (literalsBelow.contains(n.pivot._1)) {
            n.left = deletedSubProof
            n.right.literalsBelow += (n -> literalsBelow)
          }
          else { // if (literalsBelow.contains(n.pivot._2))
            n.right = deletedSubProof
            n.left.literalsBelow += (n -> literalsBelow)
          }
          regularize(n.left)
          regularize(n.right)
        }
      }
    }
  }

  def recyclePivot(proof:ResolutionProof): Unit = {
    if (proof.isInstanceOf[Resolvent]) {
      val n = proof.asInstanceOf[Resolvent]
      if (allChildrenAreVisited(proof)) {
        if (proof.children.length > 1) {
          n.left.literalsBelow += (n -> new HashSet[Literal])
          n.right.literalsBelow += (n -> new HashSet[Literal])
        }
        else if (proof.children.length == 0) {
          n.left.literalsBelow += (n -> (new HashSet[Literal] + n.pivot._2))
          n.right.literalsBelow += (n -> (new HashSet[Literal] + n.pivot._1))
        }
        else {
          val literalsBelow = n.literalsBelow.get(n.children.head) match {case Some(set) => set; case None => throw new Exception("Literals Below was not initialized properly") }
          if (!literalsBelow.contains(n.pivot._1) && !literalsBelow.contains(n.pivot._2)) {
            n.left.literalsBelow += (n -> (literalsBelow.clone + n.pivot._2))
            n.right.literalsBelow += (n -> (literalsBelow.clone + n.pivot._1))
          }
          else if (literalsBelow.contains(n.pivot._1)) {
            n.left = deletedSubProof
            n.right.literalsBelow += (n -> literalsBelow)
          }
          else { // if (literalsBelow.contains(n.pivot._2))
            n.right = deletedSubProof
            n.left.literalsBelow += (n -> literalsBelow)
          }
        }
        regularize(n.left)
        regularize(n.right)
      }
    }
  }

  def fixProof(proof:ResolutionProof) = fixProofRec(proof, new HashSet[ResolutionProof])
  private def fixProofRec(proof:ResolutionProof, visitedProofs: HashSet[ResolutionProof]) : Unit = {
    if (!visitedProofs.contains(proof)) {
      visitedProofs += proof
      proof match {
        case Input(c) => return
        case Resolvent(left,right) => {
          val n = proof.asInstanceOf[Resolvent]
          fixProofRec(left, visitedProofs)
          fixProofRec(right, visitedProofs)
          if (left.clause.contains(n.pivot._1) && right.clause.contains(n.pivot._2)) {
            n.clause = resolve(left.clause, right.clause)
          }
          else {
            val survivingParent : ResolutionProof =
            if (left == deletedSubProof) right
            else if (right == deletedSubProof) left
            else if (left.clause.contains(n.pivot._1) && !right.clause.contains(n.pivot._2)) right
            else if (!left.clause.contains(n.pivot._1) && right.clause.contains(n.pivot._2)) left
            else {
              if (proofLength(left) < proofLength(right)) left
              else right
            }
            for (child <- n.children) {
              if (child.left == n) child.left = survivingParent
              else child.right = survivingParent
            }
          }
        }
      }
    }
  }

  def allChildrenAreVisited(proof:ResolutionProof): Boolean = {
    for (child <- proof.children) {
      if (!proof.literalsBelow.contains(child)) return false
    }
    return true
  }
}
