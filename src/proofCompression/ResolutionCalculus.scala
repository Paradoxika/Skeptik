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


//  abstract class LiteralId {
//    def getInputs: List[Input]
//  }
//  case class LLeaf(input: Input) extends LiteralId {
//    def getInputs = input::Nil
//  }
//  case class LSplit(copyNumber: Int, tail: LiteralId) extends LiteralId {
//    def getInputs = tail.getInputs
//  }
//  case class LContract(left:LiteralId,right:LiteralId) extends LiteralId {
//    def getInputs = left.getInputs:::right.getInputs
//  }



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
  abstract class Proof {
    def clause : Clause  // the final clause of the proof
    val id = ProofCounter.get
    var children : List[Resolvent] = Nil
    var literalsBelow = new mutable.HashMap[Resolvent,List[Literal]]
    var pivotAtomsAbove : mutable.HashSet[Atom]
    def duplicate : Proof = {
      val visitedProofs = new mutable.HashMap[Proof,Proof]
      def duplicateRec(p: Proof) : Proof = {
        if (visitedProofs.contains(p)) return visitedProofs(p)
        else {
          val newProof = p match {
            case Resolvent(l,r) => new Resolvent(duplicateRec(l), duplicateRec(r))
            case Input(c) => new Input(c)
          }
          visitedProofs += (p -> newProof)
          return newProof
        }
      }
      duplicateRec(this)
    }
    def replaces(that: Proof) = {
      require(clause == that.clause)
      for (c <- that.children) {
        children = c::children
        if (c.left == that) c.left = this
        else c.right = this
        c.update
      }
      that.children = Nil
    }
    def isBelow(that: Proof): Boolean = {
      if (id == that.id) return true
      else this match {
        case Input(_) => return false
        case Resolvent(l,r) => return (l isBelow that) || (r isBelow that)
      }
    }
    def unsatCore = {
      val visitedProofs = new mutable.HashSet[Proof]
      def unsatCoreRec(p: Proof) : List[Input] = {
        if (!visitedProofs.contains(p)) {
          visitedProofs += p
          p match {
            case Input(c) => p.asInstanceOf[Input]::Nil
            case Resolvent(left, right) => unsatCoreRec(left):::unsatCoreRec(right)
          }
        } else Nil
      }
      unsatCoreRec(this)
    }
    def length : Int = {
      val visitedProofs = new mutable.HashSet[Proof]
      def rec(p: Proof) : Int = {
        if (!visitedProofs.contains(p)) {
          visitedProofs += p
          p match {
            case Input(c) => 1
            case Resolvent(left, right) => (rec(left) + rec(right) + 1)
          }
        } else 0
      }
      rec(this)
    }
    def literalCount : Int = {
      val visitedProofs = new mutable.HashSet[Proof]
      def rec(p: Proof) : Int = {
        if (!visitedProofs.contains(p)) {
          visitedProofs += p
          p match {
            case Input(c) => c.size
            case Resolvent(left, right) => (rec(left) + rec(right) + p.clause.size)
          }
        } else 0
      }
      rec(this)
    }
    def size : Int = {
      val visitedProofs = new mutable.HashSet[Proof]
      def rec(p: Proof) : Int = {
        if (!visitedProofs.contains(p)) {
          visitedProofs += p
          val namingCost = if (p.children.length > 1) 1 else 0
          p match {
            case Input(c) => c.size + 2*namingCost
            case Resolvent(left, right) => (rec(left) + rec(right) + 1 + 2*namingCost)
          }
        } else 1
      }
      rec(this)
    }
    def treeLength : Int = {
      val visitedProofs = new mutable.HashMap[Proof,Int]
      def rec(p: Proof) : Int = {
        if (!visitedProofs.contains(p)) {
          val result = p match {
            case Input(c) => 1
            case Resolvent(left, right) => (rec(left) + rec(right) + 1)
          }
          visitedProofs += (p -> result)
          result
        } else visitedProofs(p)
      }
      rec(this)
    }
    def nonTreeness : Double = {
      val visitedProofs = new mutable.HashSet[Proof]
      def rec(p: Proof) : Int = {
        if (!visitedProofs.contains(p)) {
          visitedProofs += p
          val countIfHasManyChildren = if (p.children.length > 1) 1 else 0
          p match {
            case Input(c) => countIfHasManyChildren
            case Resolvent(left, right) => (rec(left) + rec(right) + countIfHasManyChildren)
          }
        } else return 0
      }
      1.0*rec(this)/length
    }
    def averageNumberOfChildren : Double = {
      val visitedProofs = new mutable.HashSet[Proof]
      def rec(p: Proof) : Int = {
        if (!visitedProofs.contains(p)) {
          visitedProofs += p
          p match {
            case Input(c) => p.children.length
            case Resolvent(left, right) => rec(left) + rec(right) + p.children.length
          }
        } else 0
      }
      (1.0*rec(this))/length
    }
    def getAllSubproofs(measure: Proof => Int): List[Proof] = {
      val visitedProofs = new mutable.HashSet[Proof]
      def rec(p: Proof): List[Proof] = {
        if (visitedProofs.contains(p)) return Nil
        else {
          visitedProofs += p
          p match {
            case Input(_) => p::Nil
            case Resolvent(l,r) => insert(p, merge(rec(l),rec(r),measure),measure)
          }
        }
      }
      rec(this)
    }

    def getSubproof(id: Int) = {
      val visitedProofs = new mutable.HashMap[Proof, Proof]
      def rec(p: Proof): Proof = {
        if (visitedProofs.contains(p)) return visitedProofs(p)
        else {
          val result: Proof =
            if (p.id == id) p
            else {
              p match {
                case Input(_) => null
                case Resolvent(l,r) => {
                  val lR = rec(l)
                  if (lR != null) lR
                  else {
                    val rR = rec(r)
                    if (rR != null) rR else null
                  }
                }
              }
            }
          visitedProofs += (p -> result)
          return result
        }
      }
      rec(this)
    }
  }
  case class Input(clause: Clause) extends Proof {
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
  case class Resolvent(var left: Proof, var right: Proof) extends Proof {
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
  
}
