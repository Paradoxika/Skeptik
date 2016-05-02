package at.logic.skeptik.parser

import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import scala.util.parsing.combinator._
import at.logic.skeptik.proof.Proof
import collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula._

/**
 * The grammar for traces is:
 *    
 * <trace>       = { <clause> }
 * <clause>      = <pos> <literals> <antecedents>
 * <literals>    = "*" | { <lit> } "0"
 * <antecedents> = { <pos> } "0"
 * <lit>         = <pos> | <neg>
 * <pos>         =  "1" |  "2" | .... | <max-idx>
 * <neg>         = "-"<pos>
 * 
 * Additionally, an ordered trace satisfies the additional conditions that:
 * 
 * 1) antecedents must be resolved from left to right; 
 * 
 * 2) for a clause N with antecedents A_1, A_2,... A_m, 
 *    it must be the case that A_i < N and A_i occurs above N in the file.
 *    
 * Thanks to the ordering, more efficient parsing is possible.   
 */

object ProofParserTraceCheckOrdered extends ProofCombinatorParser[Node] with TraceCheckOrderedParsers

trait TraceCheckOrderedParsers
extends BasicTraceCheckParsers {
  def reset() = {
    proofMap = new MMap[Int,Node]
    varMap = new MMap[Int,E]
  }
  
  private var proofMap = new MMap[Int,Node]

  def proof: Parser[Proof[Node]] = rep(clause) ^^ { list => 
    Proof(list.last)
  }
  
  def clause: Parser[Node] = pos ~ literals ~ antecedents ^^ {
    case ~(~(p, l), List()) => {
        if (l.isEmpty) throw new Exception("Invalid input")
        else {
          val ax = new Axiom(l)
          proofMap += (p -> ax)
          ax
        }
      }
    case ~(~(p, l), a) => {
      val n = a.tail.foldLeft(getNode(a.head)) ({ 
        (left, right) => {
            val r = getNode(right)
            R(left, r)
          }
        })
      proofMap += (p -> n)
      n
    }
    case wl => throw new Exception("Wrong line " + wl)
  }
  
  def getNode(index: Int) = proofMap.getOrElse(index, throw new Exception("Clause not defined yet"))
  
}