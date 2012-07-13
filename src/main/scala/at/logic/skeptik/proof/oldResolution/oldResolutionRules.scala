package at.logic.skeptik.proof.oldResolution

import collection._

object typeAliases {
  type Atom = Int
  type Literal = L
  type Clause = immutable.Set[Literal]
}
import typeAliases._

case class L(atom: Atom, polarity: Boolean) {
  def dual(that: L) = (atom == that.atom && polarity != that.polarity)
  override def toString = {
    if (polarity) atom.toString
    else "-" + atom
  }
}

object defs {
  def pivotLiterals(c1: Clause, c2: Clause) : (Literal,Literal) = {
    for (l1 <- c1; l2 <- c2) {
      if (l1 dual l2) return (l1, l2)
    }
    throw new Exception("No pivots found: " + c1 + " ; " + c2)
  }
  def resolve(c1: Clause, c2: Clause): Clause = {
    val (pl1, pl2) = pivotLiterals(c1,c2)
    val contractedLiterals = for (l1 <- c1 if c2 contains l1) yield (l1, c2.find(l2 => l1 == l2).get)
    val newLiterals = for ((l1,l2) <- contractedLiterals) yield {
      val newL = l1
      newL
    }
    return (c1 - pl1 -- contractedLiterals.map(pair => pair._1)) ++
           (c2 - pl2 -- contractedLiterals.map(pair => pair._2)) ++
           newLiterals
  }
  
  val deletedSubProof = new Input(immutable.HashSet(L(Int.MaxValue,true),L(Int.MaxValue,false)))

  def length(proof:Proof) : Int = {
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
    rec(proof)
  }
}
import defs._


object Clause {
  def apply(literals: Literal*) = immutable.HashSet(literals)
}



abstract class Proof {
  def clause : Clause  
  var children : List[Resolvent] = Nil
  
  private var lB : mutable.HashMap[Resolvent,mutable.HashSet[Literal]] = null
  def literalsBelow = if (lB != null) lB
              else {lB = new mutable.HashMap[Resolvent,mutable.HashSet[Literal]]; lB}

  def forgetLiteralsBelow = lB = null

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
    //require(clause == that.clause)
    for (c <- that.children) {
      children = c::children
      if (c.left == that) c.left = this
      else c.right = this
      //c.update
    }
    that.children = Nil
  }

  def replacesAsParentOf(that: Proof, child: Resolvent) = {
    children = child::children
    if (child.left == that) child.left = this
    else child.right = this
    that.children = that.children.filterNot(_ == child)
  }

  def replacesLeftParentOf(child: Resolvent) = {
    children = child::children
    child.left.children = child.left.children.filterNot(_ == child)
    child.left = this
  }

  def replacesRightParentOf(child: Resolvent) = {
    children = child::children
    child.right.children = child.right.children.filterNot(_ == child)
    child.right = this
  }

  def delete : Unit = {
    for (c <- children) {
      if (c.left == this) c.left = deletedSubProof
      else c.right = deletedSubProof
      deletedSubProof.children = c::deletedSubProof.children
    }
    children = Nil
    if (this.isInstanceOf[Resolvent]) {
      val r = this.asInstanceOf[Resolvent]
      r.left.children = r.left.children.filterNot(_ == r)
      r.right.children = r.right.children.filterNot(_ == r)
      r.forget
    }
  }

  

  def isBelow(that: Proof): Boolean = {
    if (this == that) return true
    else this match {
      case Input(_) => return false
      case Resolvent(l,r) => return (l isBelow that) || (r isBelow that)
    }
  }
}
class Input(val clause: Clause) extends Proof {
  override def toString: String = {
    if (clause.isEmpty) "{}"
    else {
      var string = "{" + clause.head
      for (lit <- clause.tail) string += ("," + lit)
      string + "}"
    }
  }
}
object Input {
  def apply(clause: Clause) = new Input(clause)
  def unapply(p:Proof) = p match {
    case i:Input => Some(i.clause)
    case _ => None
  }
}
class Resolvent(var left: Proof, var right: Proof) extends Proof {
  private var c : Clause = null
  def clause = if (c != null) c
                        else {update; c}

  private var p : (Literal,Literal) = null
  def pivot = {
    if (p != null) p
    else {update; p}
  }
  def resolvedAtom = pivot._1.atom

  left.children = this::left.children
  right.children = this::right.children
  
  def update = {
    c = resolve(left.clause,right.clause)
    p = pivotLiterals(left.clause, right.clause)
  }
  def forget = {
    c = null
    p = null
  }
  def forgetClause = {
    c = null
  }

  def duplicateRoot = new Resolvent(left,right)

  override def toString: String = {
    var string = "(" + left + "." + right + ")"
    return string
  }
}
object Resolvent {
  def apply(left: Proof, right: Proof) = new Resolvent(left, right)
  def unapply(p:Proof) = p match {
    case r:Resolvent => Some((r.left,r.right))
    case _ => None
  }
}




