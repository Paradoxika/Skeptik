/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

import scala.collection.mutable._



object ResolutionCalculus {
  type Atom = String
  case class L(atom: Atom, polarity: Boolean) {
    var ancestorInputClauses: List[Clause] = null
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
    override def toString: String = {
      if (clause.isEmpty) return "{}"
      else {
        var string = "{" + clause.head
        for (lit <- clause.tail) string += ("," + lit)
        string += "}"
        return string
      }
    }
  }
  case class Resolvent(left: ResolutionProof, right: ResolutionProof) extends ResolutionProof {
    private var resolvent: Option[Clause] = None
    private var resolvedLiterals: Option[(Literal,Literal)] = None
    def clause : Clause = resolvent match {
      case Some(c) => return c
      case None => {
        val c = resolve(left.clause, right.clause)
        resolvent = Some(c)
        return c
      }
    }
    def pivot : (Literal,Literal) = resolvedLiterals match {
      case Some(litPair) => litPair
      case None => {
        val p = findResolvedLiterals(left.clause, right.clause)
        resolvedLiterals = Some(p)
        return p
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

  def findResolvedLiterals(clause1: Clause, clause2: Clause) : (Literal,Literal) = {
    for (l1 <- clause1; l2 <- clause2) {
      if (l1.atom == l2.atom && l1.polarity != l2.polarity) return (l1, l2)
    }
    throw new Exception("No resolved literals found...")
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


  def setAncestorInputClausesInLiteral(proof: ResolutionProof) =  setAncestorInputClausesInLiteralRec(proof,
                                          new HashSet[ResolutionProof])
  def setAncestorInputClausesInLiteralRec(proof: ResolutionProof,
                                          visitedProofs: HashSet[ResolutionProof]): Unit =
    if (!visitedProofs.contains(proof)) {
      proof match {
        case Input(c) => {
          println("Up Input Clause: " + proof.clause)
          def initializeAncestors(lit:Literal) = lit.ancestorInputClauses = c::Nil
          c.foreach(initializeAncestors)
          visitedProofs += proof
          println("Down Input Clause: " + proof.clause)
          //for (lit <- proof.clause) {
          //  require( lit.ancestorInputClauses != null )
          //}
          for ( p <- visitedProofs) {
            var corrupted = false
            var corruptedLiterals: List[Literal] = Nil
            for (lit <- p.clause) {
              if (lit.ancestorInputClauses == null) {
                corrupted = true
                corruptedLiterals = lit::corruptedLiterals
              }
            }
            if (corrupted) {
              println("Corrupted proof with clause: " + p.clause )
              println("Corrupted literals: " + corruptedLiterals)
            }
          }
        }
        case Resolvent(left, right) => {
          println("Up Clause: " + proof.clause)
          setAncestorInputClausesInLiteralRec(left, visitedProofs)
          setAncestorInputClausesInLiteralRec(right, visitedProofs)
          for ( p <- visitedProofs) {
            var corrupted = false
            var corruptedLiterals: List[Literal] = Nil
            for (lit <- p.clause) {
              if (lit.ancestorInputClauses == null) {
                corrupted = true
                corruptedLiterals = lit::corruptedLiterals
              }
            }
            if (corrupted) {
              println("Corrupted proof with clause: " + p.clause )
              println("Corrupted literals: " + corruptedLiterals)
            }
            else {
              //println("Ok proof with clause: " + p.clause )
            }
          }
          for (lit <- left.clause) {
            println("Literal: " + lit + "; ancestors: " + lit.ancestorInputClauses)
            //require( lit.ancestorInputClauses != null )
          }
          for (lit <- right.clause) {
            println("Literal: " + lit + "; ancestors: " + lit.ancestorInputClauses)
            //require( lit.ancestorInputClauses != null )
          }


          for (lit <- proof.clause) {
            val litLeftOption = left.clause.find(l => l == lit)
            val litRightOption = right.clause.find(l => l == lit)
//            if (lit.atom == "v53") {
//              println(" ")
//              println("Clause: " + proof.clause)
//              println("Left Clause: " + left.clause)
//              println("Left Visited: " + visitedProofs.contains(left))
//              println("Right Clause: " + right.clause)
//              println("Right Visited: " + visitedProofs.contains(right))
//              println("loop iteration with lit = " + lit + " : " + litLeftOption + " : " + litRightOption )
//            }
            (litLeftOption, litRightOption) match {
              case (Some(litLeft), Some(litRight)) => {
//                  if (lit.atom == "v53") {
//                    println("YAAAAAA")
//                    println(litLeft.ancestorInputClauses)
//                    println(litRight.ancestorInputClauses)
//                  }
                  lit.ancestorInputClauses = litLeft.ancestorInputClauses:::litRight.ancestorInputClauses // appends the two lists
              }
              case (Some(litLeft), None) => {
//                  if (lit.atom == "v53") {println(litLeft.ancestorInputClauses);val a = litLeft.ancestorInputClauses.head}
                  lit.ancestorInputClauses = litLeft.ancestorInputClauses
              }
              case (None, Some(litRight)) => {
//                  if (lit.atom == "v53") println(litRight.ancestorInputClauses)
                  lit.ancestorInputClauses = litRight.ancestorInputClauses
              }
              case (None, None) => throw new Exception("Literal has no ancestor!! But it should have! Something went terribly wrong...")
            }
          }
          visitedProofs += proof
          println("Down Clause: " + proof.clause)
          for ( p <- visitedProofs) {
            var corrupted = false
            var corruptedLiterals: List[Literal] = Nil
            for (lit <- p.clause) {
              if (lit.ancestorInputClauses == null) {
                corrupted = true
                corruptedLiterals = lit::corruptedLiterals
              }
            }
            if (corrupted) {
              println("Corrupted proof with clause: " + p.clause )
              println("Corrupted literals: " + corruptedLiterals)
            }
          }
//          for (lit <- proof.clause) {
//            require( lit.ancestorInputClauses != null )
//          }
        }
      }
    } else {
      println("Visited Clause: " + proof.clause)
    }

  def proofLength(proof: ResolutionProof): Int = proofLengthRec(proof, new HashSet[ResolutionProof])
  def proofLengthRec(proof: ResolutionProof, visitedProofs: HashSet[ResolutionProof]) : Int =
    if (!visitedProofs.contains(proof)) {
      visitedProofs += proof
      proof match {
        case Input(c) => return 0
        case Resolvent(left, right) => {
          return (proofLengthRec(left, visitedProofs) + proofLengthRec(right, visitedProofs) + 1)
        }
      }
    } else return 0
}
