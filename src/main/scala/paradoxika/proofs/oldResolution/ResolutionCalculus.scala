package ResK.calculi

import scala.collection._


//object simpleResolution {
//  type Atom = Int
//
//  case class Clause(ant:immutable.Set[Atom],suc:immutable.Set[Atom]) {
//    def *(that:Clause) = suc.find(a => that.ant.contains(a)) match {
//      case None => throw new Exception("Clauses are not resolvable.")
//      case Some(a) => (a, (this - a) ++ (a -: that))
//    }
//    
//    override def toString = (("" + ant.head) /: ant.tail)((s,atom) => s + "," + atom) + ":-" +
//                            (("" + suc.head) /: suc.tail)((s,atom) => s + "," + atom)
//  }
//
//  abstract class Proof {
//    def clause : Clause  
//
//    def duplicate : Proof = {
//      val visitedProofs = new mutable.HashMap[Proof,Proof]
//      def duplicateRec(p: Proof) : Proof = {
//        if (visitedProofs.contains(p)) return visitedProofs(p)
//        else {
//          val newProof = p match {
//            case R(l,r) => new R(duplicateRec(l), duplicateRec(r))
//            case I(c) => new I(c)
//          }
//          visitedProofs += (p -> newProof)
//          return newProof
//        }
//      }
//      duplicateRec(this)
//    }
//  }
//  class I(val clause: Clause) extends Proof {
//    override def toString: String = clause.toString
//  }
//  object I {
//    def apply(clause: Clause) = new I(clause)
//    def unapply(p:Proof) = p match {
//      case i:I => Some(i.clause)
//      case _ => None
//    }
//  }
//  class R(val left: Proof, val right: Proof) extends Proof {
//    val clause = (left.clause * right.clause)
//    val pivot : (Literal,Literal) = (left.clause pivotLiterals right.clause)
//
//    override def toString = "(" + left + "." + right + ")"
//  }
//  object R {
//    def apply(left: Proof, right: Proof) = new R(left, right)
//    def unapply(p:Proof) = p match {
//      case r:R => Some((r.left,r.right))
//      case _ => None
//    }
//  }
//  
//  object measures {
//    def length(proof:Proof) : Int = {
//      val visitedProofs = new mutable.HashSet[Proof]
//      def rec(p: Proof) : Int = {
//        if (!visitedProofs.contains(p)) {
//          visitedProofs += p
//          p match {
//            case I(c) => 1
//            case R(left, right) => (rec(left) + rec(right) + 1)
//          }
//        } else 0
//      }
//      rec(proof)
//    }
//  }
//
//  
//}


object resolution {
  type Atom = Int
  case class L(atom: Atom, polarity: Boolean) {
    def dual(that: L) = (atom == that.atom && polarity != that.polarity)
    override def toString = {
      if (polarity) atom.toString
      else "-" + atom
    }
  }
  type Literal = L


  type Clause = immutable.Set[Literal]
  object Clause {
    def apply(literals: Literal*) = immutable.HashSet(literals)
  }
  def pivotLiterals(c1: Clause, c2: Clause) : (Literal,Literal) = {
    for (l1 <- c1; l2 <- c2) {
      if (l1 dual l2) return (l1, l2)
    }
    throw new Exception("No pivots found: " + c1 + " ; " + c2)
  }
  def resolve(c1: Clause, c2: Clause): Clause = {
    val (pl1, pl2) = pivotLiterals(c1,c2)
    val contractedLiterals = for (l1 <- c1 if c2 contains l1) yield (l1, c2.find(l2 => l1 == l2).get) // ToDo: Improve efficiency
    val newLiterals = for ((l1,l2) <- contractedLiterals) yield {
      val newL = l1
      newL
    }
    return (c1 - pl1 -- contractedLiterals.map(pair => pair._1)) ++
           (c2 - pl2 -- contractedLiterals.map(pair => pair._2)) ++
           newLiterals
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
      that.children -= child
    }

    def replacesLeftParentOf(child: Resolvent) = {
      children = child::children
      child.left.children -= child
      child.left = this
    }

    def replacesRightParentOf(child: Resolvent) = {
      children = child::children
      child.right.children -= child
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
        r.left.children -= r
        r.right.children -= r
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
  
  val deletedSubProof = new Input(immutable.HashSet(L(Int.MaxValue,true),L(Int.MaxValue,false)))
  
  
  object measures {
  //    def unsatCore = {
  //      val visitedProofs = new mutable.HashSet[Proof]
  //      def unsatCoreRec(p: Proof) : List[Input] = {
  //        if (!visitedProofs.contains(p)) {
  //          visitedProofs += p
  //          p match {
  //            case Input(c) => p.asInstanceOf[Input]::Nil
  //            case Resolvent(left, right) => unsatCoreRec(left):::unsatCoreRec(right)
  //          }
  //        } else Nil
  //      }
  //      unsatCoreRec(this)
  //    }
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
  //    def literalCount : Int = {
  //      val visitedProofs = new mutable.HashSet[Proof]
  //      def rec(p: Proof) : Int = {
  //        if (!visitedProofs.contains(p)) {
  //          visitedProofs += p
  //          p match {
  //            case Input(c) => c.size
  //            case Resolvent(left, right) => (rec(left) + rec(right) + p.clause.size)
  //          }
  //        } else 0
  //      }
  //      rec(this)
  //    }
  //    def size : Int = {
  //      val visitedProofs = new mutable.HashSet[Proof]
  //      def rec(p: Proof) : Int = {
  //        if (!visitedProofs.contains(p)) {
  //          visitedProofs += p
  //          val namingCost = if (p.children.length > 1) 1 else 0
  //          p match {
  //            case Input(c) => c.size + 2*namingCost
  //            case Resolvent(left, right) => (rec(left) + rec(right) + 1 + 2*namingCost)
  //          }
  //        } else 1
  //      }
  //      rec(this)
  //    }
  //    def treeLength : Int = {
  //      val visitedProofs = new mutable.HashMap[Proof,Int]
  //      def rec(p: Proof) : Int = {
  //        if (!visitedProofs.contains(p)) {
  //          val result = p match {
  //            case Input(c) => 1
  //            case Resolvent(left, right) => (rec(left) + rec(right) + 1)
  //          }
  //          visitedProofs += (p -> result)
  //          result
  //        } else visitedProofs(p)
  //      }
  //      rec(this)
  //    }
  //    def nonTreeness : Double = {
  //      val visitedProofs = new mutable.HashSet[Proof]
  //      def rec(p: Proof) : Int = {
  //        if (!visitedProofs.contains(p)) {
  //          visitedProofs += p
  //          val countIfHasManyChildren = if (p.children.length > 1) 1 else 0
  //          p match {
  //            case Input(c) => countIfHasManyChildren
  //            case Resolvent(left, right) => (rec(left) + rec(right) + countIfHasManyChildren)
  //          }
  //        } else return 0
  //      }
  //      1.0*rec(this)/length
  //    }
  //    def averageNumberOfChildren : Double = {
  //      val visitedProofs = new mutable.HashSet[Proof]
  //      def rec(p: Proof) : Int = {
  //        if (!visitedProofs.contains(p)) {
  //          visitedProofs += p
  //          p match {
  //            case Input(c) => p.children.length
  //            case Resolvent(left, right) => rec(left) + rec(right) + p.children.length
  //          }
  //        } else 0
  //      }
  //      (1.0*rec(this))/length
  //    }
  //    def getAllSubproofs(measure: Proof => Int): List[Proof] = {
  //      val visitedProofs = new mutable.HashSet[Proof]
  //      def rec(p: Proof): List[Proof] = {
  //        if (visitedProofs.contains(p)) return Nil
  //        else {
  //          visitedProofs += p
  //          p match {
  //            case Input(_) => p::Nil
  //            case Resolvent(l,r) => insert(p, merge(rec(l),rec(r),measure),measure)
  //          }
  //        }
  //      }
  //      rec(this)
  //    }

  //    def getSubproof(proof: Proof) = {
  //      val visitedProofs = new mutable.HashMap[Proof, Proof]
  //      def rec(p: Proof): Proof = {
  //        if (visitedProofs.contains(p)) return visitedProofs(p)
  //        else {
  //          val result: Proof =
  //            if (p == proof) p
  //            else {
  //              p match {
  //                case Input(_) => null
  //                case Resolvent(l,r) => {
  //                  val lR = rec(l)
  //                  if (lR != null) lR
  //                  else {
  //                    val rR = rec(r)
  //                    if (rR != null) rR else null
  //                  }
  //                }
  //              }
  //            }
  //          visitedProofs += (p -> result)
  //          return result
  //        }
  //      }
  //      rec(this)
  //    }

  }

  
}
