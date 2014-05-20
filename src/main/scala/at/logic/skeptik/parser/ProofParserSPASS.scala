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
 def proof: Parser[Proof[Node]] = rep(line) ^^ {   
 	case list =>{ 
 		val p = Proof((list.last).last)
 		exprMap = new MMap[String,E]
 		p
    }
  }
  
  
  def line: Parser[List[Node]] = lineNum ~ lineSummary ~ proofLine ^^ {
  	_ => List();//change this
  }
  
  def proofLine: Parser[String] = rep(proofTerm) ~ "->" ~ rep(proofTerm)  ~ "." ^^{ 
    _ => "" //TODO: return something meaningful
  }	
  
  def proofTerm: Parser[String] = (term | term ~ "*") ^^{
    _ => "" //TODO: return something meaningful
  }
  
  def lineNum: Parser[Int] = number
  
  def lineSummary: Parser[String] = "[" ~ lineType ~ rep(lineRef) ~ "] ||" ^^{
    _ => "" //TODO: return something meaningful
  }
  
  def lineRef: Parser[String] = (ref ~ "," | ref) ^^{
    _ => "" //TODO: return something meaningful
  }
  
  //TODO: test this--does the regex parse decimals?
  def ref: Parser[String] = number ~ "." ~ number ^^ {
	  _ => "" //TODO: return something meaningful
  }
  
  def lineType: Parser[Int] = number ~ ":" ~ typeName ^^ {
    case ~(~(n,_),_) => n
  }
  
  def typeName: Parser[String] = "Inp" | "Res:" | "Spt:" | "Con:"
  
  def cnfName: Parser[String] = name ^^ {
    case _ => {
      println("sos")
      "sos"
    }
  }
    
  def cnfRole: Parser[String] = name ^^ {
    case _ => {
      println("axiom")
      "axiom"
    }
  }

  def func: Parser[String] = equals | max | userDef | lessEquals | greaterEquals
  
  def equals: Parser[String] = "eq(" ~ term ~ "," ~ term ~ ")" ^^ {
      case ~(~(~(~(_,first),_),second),_) => {
      println("eq: " + first + " " + second)
      "eq"
    }
  }
  
    def lessEquals: Parser[String] = "le(" ~ term ~ "," ~ term ~ ")" ^^ {
      case ~(~(~(~(_,first),_),second),_) => {
      println("le: " + first + " " + second)
      "le"
    }
  }
  
    
    def greaterEquals: Parser[String] = "ge(" ~ term ~ "," ~ term ~ ")" ^^ {
      case ~(~(~(~(_,first),_),second),_) => {
      println("ge: " + first + " " + second)
      "ge"
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
  
  def number: Parser[Int] = """\d+""".r ^^ { _.toInt }
  
  def term: Parser[String] = ("(~ " ~ term ~ ")" | func | num | str) ^^ {
    case _ => {
      println("term")
      ""
    }
  }
    
    
  def cnfFormula: Parser[String] = term ~ "|" ~ term ~ "|" ~ term ^^ { //This is actually a disjunction in the BNF of TPTP, and as such, might not always have 3 conjunctions
    case _ => {
      println("line")
      ""
    }
  }
   
    def str: Parser[String] = """[^ ():]+""".r ^^ {
      case s => {
        println("str: " + s)
        s
      }
    }
    
    def name: Parser[String] = """[^ (){}:⊢,.=]+""".r ^^ {
      case s => {
        println("name: " + s)
        s
      }
    }
    
}
