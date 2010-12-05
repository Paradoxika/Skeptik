/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import scala.collection._
//import scala.collection.mutable._
import proofCompression.Utilities._


object ResolutionCalculus {
  type Atom = String
  case class L(atom: Atom, polarity: Boolean) {
    var ancestorInputs: List[Input] = Nil
    def dual(that: L) = (atom == that.atom && polarity != that.polarity)
    override def toString = {
      if (polarity) atom
      else "-" + atom
    }
  }
  type Literal = L


  abstract class LiteralId {
    def getInputs: List[Input]
  }
  case class LLeaf(input: Input) extends LiteralId {
    def getInputs = input::Nil
  }
  case class LSplit(copyNumber: Int, tail: LiteralId) extends LiteralId {
    def getInputs = tail.getInputs
  }
  case class LContract(left:LiteralId,right:LiteralId) extends LiteralId {
    def getInputs = left.getInputs:::right.getInputs
  }



  type Clause = immutable.Set[Literal]
  object Clause {
    def apply(literals: Literal*) = immutable.HashSet(literals)
  }
  def pivotLiterals(c1: Clause, c2: Clause) : (Literal,Literal) = {
    for (l1 <- c1; l2 <- c2) {
      if (l1 dual l2) return (l1, l2)
    }
    throw new Exception("No pivots found...")
  }
  def resolve(c1: Clause, c2: Clause): Clause = {
    val (pl1, pl2) = pivotLiterals(c1,c2)
    val contractedLiterals = for (l1 <- c1 if c2 contains l1) yield (l1, c2.find(l2 => l1 == l2).get)
    val newLiterals = for ((l1,l2) <- contractedLiterals) yield {
      val newL = new L(l1.atom, l1.polarity)
      newL.ancestorInputs = l1.ancestorInputs:::l2.ancestorInputs
      newL
    }
    return (c1 - pl1 -- contractedLiterals.map(pair => pair._1)) ++
           (c2 - pl2 -- contractedLiterals.map(pair => pair._2)) ++
           newLiterals
  }
  


  val ProofCounter = new Counter
  abstract class ResolutionProof {
    def clause : Clause  // the final clause of the proof
    val id = ProofCounter.get
    var children : List[Resolvent] = Nil
    var literalsBelow = new mutable.HashMap[Resolvent,List[Literal]]
    var pivotAtomsAbove : mutable.HashSet[Atom]
    def duplicate : ResolutionProof = {
      def duplicateRec(proof: ResolutionProof, visitedProofs: mutable.HashMap[ResolutionProof,ResolutionProof]) : ResolutionProof = {
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
      duplicateRec(this, new mutable.HashMap[ResolutionProof,ResolutionProof])
    }
    def replaces(that: ResolutionProof) = {
      for (c <- that.children) {
//        println(c.clause)
//        println(c.pivot)
//        println(c.left.clause)
//        println(c.right.clause)
//        println(clause)
//        println()
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
    var pivotAtomsAbove = new mutable.HashSet[Atom]
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
    var clause : Clause = resolve(left.clause,right.clause)
    var pivot : (Literal,Literal) = pivotLiterals(left.clause,right.clause)
    def resolvedAtom = pivot._1.atom
    var pivotAtomsAbove = left.pivotAtomsAbove.clone.union(right.pivotAtomsAbove) + resolvedAtom

    left.children = this::left.children
    right.children = this::right.children



    def update = {
      clause = resolve(left.clause,right.clause)
      pivot = pivotLiterals(left.clause, right.clause)
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

  def getNodeById(p: ResolutionProof, id: Int, visitedProofs: mutable.HashMap[ResolutionProof, ResolutionProof]): ResolutionProof = {
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





  


  def proofLength(proof: ResolutionProof): Int = proofLengthRec(proof, new mutable.HashSet[ResolutionProof])
  def proofLengthRec(proof: ResolutionProof, visitedProofs: mutable.HashSet[ResolutionProof]) : Int =
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
