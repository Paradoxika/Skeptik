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

object ProofParserTraceCheck extends ProofParser[Node] with TraceCheckParsers

trait TraceCheckParsers
extends JavaTokenParsers with RegexParsers {
  
  private var proofMap = new MMap[Int,Node]
  private var varMap = new MMap[Int,E]

  def proof: Parser[Proof[Node]] = rep(clause) ^^ { list => 
    val p = Proof(list.last)
    println("pm: " + proofMap)
    println("vm: " + varMap)
    println("last: " + list.last)
    println("full list: " + list)
    proofMap = new MMap[Int,Node]
    p
  }
  def clause: Parser[Node] = pos ~ literals ~ antecedents ^^ {
    case ~(~(p, l), List()) => {
        if (l.isEmpty) throw new Exception("Invalid input")
        else {
          println("head:" + l.head)
          val ax = new Axiom(l)
          proofMap += (p -> ax)
          println("read axiom " + ax)
          ax
        }
      }
    
    case ~(~(p, l), a) => {
      println("a: "+ a)
      val n = a.tail.foldLeft(getNode(a.head)) ({ 
        (left, right) => {
            val r = getNode(right)
            println("trying to resolve " + left + " with " + r)
            R(left, r)
          }
        })
      proofMap += (p -> n)
      println("second case: " + n)
      n
    }
    
    
    case wl => throw new Exception("Wrong line " + wl)
  }
  
  def getNode(index: Int) = {
   // println("here?")
    proofMap.getOrElse(index, throw new Exception("Clause not defined yet"))
  }
  
  def pos: Parser[Int] = """[1-9][0-9]*""".r ^^ { _.toInt }
  
  def neg: Parser[Int] = """-[1-9][0-9]*""".r ^^ { _.toInt }
  
  def literals: Parser[List[E]] = ("*" | lits <~ "0") ^^ {
    case "*" => List()
    case l: List[E] => l
  }
  
  def lits: Parser[List[E]] = rep(lit)
  
  def lit: Parser[E] = (pos | neg) ^^ {l => 
    if (l > 0) varMap.getOrElseUpdate(l,new Var(l.toString,o))
    else varMap.getOrElseUpdate(l,new App(negC,new Var(l.abs.toString,o)))
  }
  
  def antecedents: Parser[List[Int]] = rep(pos) <~ "0"
}