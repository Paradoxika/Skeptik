/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import scala.collection.mutable._
import proofCompression.Utilities._


object ResolutionCalculus {
  type Atom = String
  case class L(atom: Atom, polarity: Boolean) {
    var ancestorInputs: List[Input] = Nil
    override def toString = {
      if (polarity) atom
      else "-" + atom
    }
  }
  type Literal = L

  type Clause = List[Literal]

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
    for (lit <- resolvent) {
      val litLeftOption = clause1.find(l => l == lit)
      val litRightOption = clause2.find(l => l == lit)
      (litLeftOption, litRightOption) match {
        case (Some(litLeft), Some(litRight)) => lit.ancestorInputs = litLeft.ancestorInputs:::litRight.ancestorInputs // appends the two lists
        case (Some(litLeft), None) => lit.ancestorInputs = litLeft.ancestorInputs
        case (None, Some(litRight)) => lit.ancestorInputs = litRight.ancestorInputs
        case (None, None) => throw new Exception("Literal has no ancestor!! But it should have! Something went terribly wrong...")
      }
    }
    return resolvent
  }

  def findPivots(clause1: Clause, clause2: Clause) : (Literal,Literal) = {
    for (l1 <- clause1; l2 <- clause2) {
      if (l1.atom == l2.atom && l1.polarity != l2.polarity) return (l1, l2)
    }
    throw new Exception("No pivots found...")
  }


  val ProofCounter = new Counter
  abstract class ResolutionProof {
    def clause : Clause  // the final clause of the proof
    val id = ProofCounter.get
    var children : List[Resolvent] = Nil
    val literalsBelow = new HashMap[Resolvent,List[Literal]]
    val pivotAtomsAbove : HashSet[Atom]
    def duplicate : ResolutionProof = {
      def duplicateRec(proof: ResolutionProof, visitedProofs: HashMap[ResolutionProof,ResolutionProof]) : ResolutionProof = {
        if (visitedProofs.contains(proof)) return visitedProofs(proof)
        else {
          val newProof = proof match {
            case Resolvent(l,r) => new Resolvent(duplicateRec(l, visitedProofs), duplicateRec(r,visitedProofs))
            case Input(c) => proof
          }
          visitedProofs += (proof -> newProof)
          return newProof
        }
      }
      duplicateRec(this, new HashMap[ResolutionProof,ResolutionProof])
    }
    def replaces(that: ResolutionProof) = {
      for (c <- that.children) {
        println(c.clause)
        println(c.pivot)
        println(c.left.clause)
        println(c.right.clause)
        println(clause)
        println()
        children = c::children
        if (c.left == that) c.left = this
        else c.right = this
        c.update
      }
      that.children = Nil
    }
    def isBelow(that: ResolutionProof): Boolean = {
      if (id == that.id) return true
      else this match {
        case Input(_) => return false
        case Resolvent(l,r) => return (l isBelow that) || (r isBelow that)
      }
    }
  }
  case class Input(clause: Clause) extends ResolutionProof {
    val pivotAtomsAbove = new HashSet[Atom]
    for (lit <- clause) lit.ancestorInputs = this::Nil
    override def toString: String = {
      if (clause.isEmpty) "{}"
      else {
        var string = "{" + clause.head
        for (lit <- clause.tail) string += ("," + lit)
        string + "}"
      }
    }
    override def hashCode = 41 + id
    override def canEqual(other:Any): Boolean = other.isInstanceOf[Input]
    override def equals(other:Any): Boolean = other match {
      case that: Input => (that canEqual this) && that.id == this.id
      case _ => false
    }
  }
  case class Resolvent(var left: ResolutionProof, var right: ResolutionProof) extends ResolutionProof {
    var clause : Clause = resolve(left.clause, right.clause)
    var pivot : (Literal,Literal) = findPivots(left.clause, right.clause)
    def resolvedAtom = pivot._1.atom
    val pivotAtomsAbove = left.pivotAtomsAbove.clone.union(right.pivotAtomsAbove)
    pivotAtomsAbove += resolvedAtom

    left.children = this::left.children
    right.children = this::right.children



    def update = {
      clause = resolve(left.clause,right.clause)
      pivot = findPivots(left.clause,right.clause)
    }


    override def toString: String = {
      var string = "(" + left + "." + right + ")"
      return string
    }
    override def hashCode = 41 + id
    override def canEqual(other:Any): Boolean = other.isInstanceOf[Resolvent]
    override def equals(other:Any): Boolean = other match {
      case that: Resolvent => (that canEqual this) && that.id == this.id
      case _ => false
    }
  }

  def getNodeById(p: ResolutionProof, id: Int, visitedProofs: HashMap[ResolutionProof, ResolutionProof]): ResolutionProof = {
    if (visitedProofs.contains(p)) return visitedProofs(p)
    else {
      var result: ResolutionProof = null
      if (p.id == id) result = p
      else {
        p match {
          case Input(_) => return null
          case Resolvent(l,r) => {
            val lR = getNodeById(l, id, visitedProofs)
            if (lR != null) result = lR
            else {
              val rR = getNodeById(r, id, visitedProofs)
              if (rR != null) result = rR
            }
          }
        }
      }
      visitedProofs += (p -> result)
      return result
    }
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

  def isNonTree(proof: ResolutionProof)  = {
    def isNonTreeRec(p: ResolutionProof): Boolean = p match {
      case Input(_) => p.children.length > 1
      case Resolvent(l, r) =>  p.children.length > 1 || isNonTreeRec(l) || isNonTreeRec(r)
    }
    isNonTreeRec(proof)
  }
}
