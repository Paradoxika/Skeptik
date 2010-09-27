/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

import scala.collection.mutable._



object ResolutionCalculus {
  type Atom = String
  case class L(atom: Atom, polarity: Boolean) {
    var ancestorInputs: List[Input] = null
    override def toString = {
      if (polarity) atom
      else "-" + atom
    }
  }
  type Literal = L

  type Clause = List[Literal]

  abstract class ResolutionProof {
    def clause : Clause  // the final clause of the proof
  }
  case class Input(clause: Clause) extends ResolutionProof {
    for (lit <- clause) lit.ancestorInputs = this::Nil
    override def toString: String = {
      if (clause.isEmpty) "{}"
      else {
        var string = "{" + clause.head
        for (lit <- clause.tail) string += ("," + lit)
        string + "}"
      }
    }
  }
  case class Resolvent(left: ResolutionProof, right: ResolutionProof) extends ResolutionProof {
    val clause : Clause = resolve(left.clause, right.clause)
    val pivot : (Literal,Literal) = findPivots(left.clause, right.clause)  
    for (lit <- clause) {
      val litLeftOption = left.clause.find(l => l == lit)
      val litRightOption = right.clause.find(l => l == lit)
      (litLeftOption, litRightOption) match {
        case (Some(litLeft), Some(litRight)) => lit.ancestorInputs = litLeft.ancestorInputs:::litRight.ancestorInputs // appends the two lists
        case (Some(litLeft), None) => lit.ancestorInputs = litLeft.ancestorInputs
        case (None, Some(litRight)) => lit.ancestorInputs = litRight.ancestorInputs
        case (None, None) => throw new Exception("Literal has no ancestor!! But it should have! Something went terribly wrong...")
      }
    }
    override def toString: String = {
      var string = "(" + left + "+" + right + ")"
      return string
    }
  }

  def resolve(clause1: Clause, clause2: Clause) : Clause = {
    var resolvent : Clause = Nil
    for (l1 <- clause1) {
      var hasMatchingLiteral = false
      for (l2 <- clause2) {
        if (l1.atom == l2.atom) {
          hasMatchingLiteral = true
          if (l1.polarity == l2.polarity) resolvent = (new L(l1.atom, l1.polarity))::resolvent
        }
      }
      if (!hasMatchingLiteral) resolvent = (new L(l1.atom, l1.polarity))::resolvent
    }
    for (l2 <- clause2) {
      var hasMatchingLiteral = false
      for (l1 <- clause1) {
        if (l1.atom == l2.atom) hasMatchingLiteral = true
      }
      if (!hasMatchingLiteral) resolvent = (new L(l2.atom, l2.polarity))::resolvent
    }
    return resolvent
  }

  def findPivots(clause1: Clause, clause2: Clause) : (Literal,Literal) = {
    for (l1 <- clause1; l2 <- clause2) {
      if (l1.atom == l2.atom && l1.polarity != l2.polarity) return (l1, l2)
    }
    throw new Exception("No pivots found...")
  }
  
  def equalClauses(clause1:Clause, clause2:Clause) : Boolean = {
    if (clause1.length == clause2.length) {
      for (l1 <- clause1) {
        clause2.find(l2 => (l2.atom == l1.atom && l2.polarity == l1. polarity)) match {
          case None => return false
          case _ =>
        }
      }
      return true
    } else return false
  }

  def proofLength(proof: ResolutionProof): Int = proofLengthRec(proof, new HashSet[ResolutionProof])
  def proofLengthRec(proof: ResolutionProof, visitedProofs: HashSet[ResolutionProof]) : Int =
    if (!visitedProofs.contains(proof)) {
      visitedProofs += proof
      proof match {
        case Input(c) => return 1
        case Resolvent(left, right) => {
          return (proofLengthRec(left, visitedProofs) + proofLengthRec(right, visitedProofs) + 1)
        }
      }
    } else return 0
}
