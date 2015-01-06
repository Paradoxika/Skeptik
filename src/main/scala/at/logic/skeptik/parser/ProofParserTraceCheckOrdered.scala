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
 * The syntax of a trace is as follows:
 *    
 * <trace>       = { <clause> }
 * <clause>      = <pos> <literals> <antecedents>
 * <literals>    = "*" | { <lit> } "0"
 * <antecedents> = { <pos> } "0"
 * <lit>         = <pos> | <neg>
 * <pos>         =  "1" |  "2" | .... | <max-idx>
 * <neg>         = "-"<pos>
 * 
 */

object ProofParserTraceCheckOrdered extends ProofCombinatorParser[Node] with TraceCheckOrderedParsers

trait TraceCheckOrderedParsers
extends BasicTraceCheckParsers {
  
  private var proofMap = new MMap[Int,Node]

  def proof: Parser[Proof[Node]] = rep(clause) ^^ { list => 
    val p = Proof(list.last)
    proofMap = new MMap[Int,Node]
    p
  }
  def clause: Parser[Node] = pos ~ literals ~ antecedents ^^ {
    case ~(~(p, l), List()) => {
        if (l.isEmpty) throw new Exception("Invalid input")
        else {
          val ax = new Axiom(l)
          proofMap += (p -> ax)
//          println("read axiom " + ax)
          ax
        }
      }
    case ~(~(p, l), a) => {
      val n = a.tail.foldLeft(getNode(a.head)) ({ 
        (left, right) => {
            val r = getNode(right)
//            println("trying to resolve " + left + " with " + r)
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