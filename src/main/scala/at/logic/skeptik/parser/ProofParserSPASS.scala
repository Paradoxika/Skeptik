package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

object ProofParserSPASS extends ProofParser[Node] with SPASSParsers

trait SPASSParsers
extends JavaTokenParsers with RegexParsers {
  
  private var proofMap = new MMap[String,Node]
  private var exprMap = new MMap[String,E]
  private var varMap = new MMap[String,E]
  
  //TODO: remove debugging lines
  //TODO: actually store the information; right now it parses the stuff and throws it away
  
  //returns the actual proof
 def proof: Parser[Proof[Node]] = rep(cnf) ^^ {   
 	case list =>{ 
 		val p = Proof((list.last).last)
 		exprMap = new MMap[String,E]
 		p
    }
  }
  
  
  def sos: Parser[String] = "sos" ^^ {
    case _ => {
      println("sos")
      "sos"
    }
  }
    
  def axiom: Parser[String] = "axiom" ^^ {
    case _ => {
      println("axiom")
      "axiom"
    }
  }

  def func: Parser[String] = equals | max | userDef
  
  def equals: Parser[String] = "eq(" ~ term ~ "," ~ term ~ ")" ^^ {
      case ~(~(~(~(_,first),_),second),_) => {
      println("eq: " + first + " " + second)
      "eq"
    }
  }
  
  def max: Parser[String] = "max(" ~ term ~ "," ~ term ~ "," ~ term ~ ")" ^^ {
    case _ => ""
  }
  
  def userDef: Parser[String] = str ~ "(" ~ term ~ ")" ^^ {
    case ~(~(~(s,_),t),_) => {
      println("userdef: " + s)
      s
    }
  }
    
  def num: Parser[String] = """\d+""".r ^^ { 
    case a => {
      println("num: " + a)
      a
    }
  }
  
  def term: Parser[String] = ("(~ " ~ term ~ ")" | func | num | str) ^^ {
    case _ => {
      println("term")
      ""
    }
  }
    
    
  def line: Parser[String] = term ~ "|" ~ term ~ "|" ~ term ^^ {
    case _ => {
      println("line")
      ""
    }
  }
    
  def cnf: Parser[List[Node]] = "cnf(" ~ sos ~ "," ~ axiom ~ "," ~ line ~ ")." ^^{
    case ~(~(~(_,_),m),_) => {
      println("cnf")
      List()//TODO: replace this
    }
  } 
  

    def str: Parser[String] = """[^ ():]+""".r ^^ {
      case s => {
        println("str: " + s)
        s
      }
    }
}
