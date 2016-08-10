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

object ParserTPTP extends ProofCombinatorParser[Node] with ParserTPTP


trait ParserTPTP
extends JavaTokenParsers with RegexParsers {
  
  private var proofMap = new MMap[String,Node]
  private var exprMap = new MMap[String,E]
  private var varMap = new MMap[String,E]

  def reset(): Unit = ()

  //Note (jgorzny; 27 Apr 2016):
  //I don't think this parser was ever completed or used (in whatever state it exists in)
  //Use *only* after testing; the TODOs below suggest some work needs to be done.
  
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
    
  def cnf: Parser[List[Node]] = "cnf(" ~ cnfName ~ "," ~ cnfRole ~ "," ~ cnfFormula ~ ")." ^^{
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
    
    def name: Parser[String] = """[^ (){}:⊢,.=]+""".r ^^ {
      case s => {
        println("name: " + s)
        s
      }
    }
}
