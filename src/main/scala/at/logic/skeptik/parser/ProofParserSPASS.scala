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
  
  private var count = 0;
  
  private var proofMap = new MMap[String,Node]
  private var exprMap = new MMap[String,E]
  private var varMap = new MMap[String,E]
  
  //TODO: remove debugging lines
  //TODO: actually store the information; right now it parses the stuff and throws it away
  
  //returns the actual proof
 def proof: Parser[Proof[Node]] = rep(line) ^^ {   
 	case list =>{ 
 	    println("parsed! " + count)
 	    println(varMap)
 	    println(exprMap)
 		val p = Proof((list.last).last)
 		exprMap = new MMap[String,E]
 		p
    }
  }
  
  
  def line: Parser[List[Node]] = lineNum ~ lineSummary ~ proofLine ^^ {
  	_ => List();//change this
  }
  
  def proofLine: Parser[String] = rep(proofTerm) ~ "->" ~ rep(proofTerm)  ~ "." ^^{ 
    _ => {
      count = count + 1
      if (count % 500 == 0) {println(count + " lines parsed")}
      //println("in proofline " + count)
      "" //TODO: return something meaningful
    }
  }	
  
  def proofTerm: Parser[String] = (term ~ "*+" | term  ~ "*" | term ~ "+" | term) ^^{
    case _ => {
      //println("in proof term ")
      "" //TODO: return something meaningful
    }
  }
  
  
  def lineNum: Parser[Int] = number
  
  def lineSummary: Parser[String] = "[" ~ lineType ~ rep(lineRef) ~ "] ||" ^^{
    _ => "" //TODO: return something meaningful
  }
  
  def lineRef: Parser[String] = (ref ~ "," | ref) ^^{
    _ => "" //TODO: return something meaningful
  }
  
  def ref: Parser[String] = number ~ "." ~ number ^^ {
    case ~(~(a,_),b) => {
	    //println(a + "  " + b)
	    "" //TODO: return something meaningful
	  }
  }
  
  def lineType: Parser[Int] = number ~ ":" ~ typeName ^^ {
    case ~(~(n,_),_) => n
  }
  
  //TODO: each one of these does NOT have a unique integer preceding it
  //TODO: get complete list from SPASS documentation
  def typeName: Parser[String] = "Inp" | "Res:" | "Spt:" | "Con:" | "MRR:" | "UnC:" 
  
  def func: Parser[E] = equals | max | userDef | lessEquals | greaterEquals
  
  def equals: Parser[E] = "eq(" ~ term ~ "," ~ term ~ ")" ^^ {
      case ~(~(~(~(_,first),_),second),_) => {
      //println("eq: " + first + " " + second)
      //can't use function like in user defined function, as there are multiple arguments and App does not support that
      exprMap.getOrElseUpdate("eq",new App2(new Var("eq",new ArrowPair(o,o,o)), first, second))
    }
  }
  
    def lessEquals: Parser[E] = "le(" ~ term ~ "," ~ term ~ ")" ^^ {
      case ~(~(~(~(_,first),_),second),_) => {
     // println("le: " + first + " " + second)
      //can't use function like in user defined function, as there are multiple arguments and App does not support that
      exprMap.getOrElseUpdate("le",new App2(new Var("le",new ArrowPair(o,o,o)), first, second))
    }
  }
  
    
  def greaterEquals: Parser[E] = "ge(" ~ term ~ "," ~ term ~ ")" ^^ {
      case ~(~(~(~(_,first),_),second),_) => {
      //println("ge: " + first + " " + second)
      //can't use function like in user defined function, as there are multiple arguments and App does not support that
      exprMap.getOrElseUpdate("ge",new App2(new Var("ge",new ArrowPair(o,o,o)), first, second))
    }
  }
    
  def max: Parser[E] = "max(" ~ term ~ "," ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(~(~(_,first),_),second),_),last),_) => {
     //last 
     //can't use function like in user defined function, as there are multiple arguments and App does not support that
      exprMap.getOrElseUpdate("max",new App3(new Var("max",new ArrowTriple(o,o,o,o)), first, second, last))
    }
    
  }
  
  def userDef: Parser[E] = name ~ "(" ~ term ~ ")" ^^ {
    case ~(~(~(name,_),arg),_) => {
      //println("userdef: " + name + " - " + arg)
      new Var(name,new Arrow(o, o))
      
      exprMap.getOrElseUpdate(name,new App(new Var(name,new Arrow(o,o)), arg))
    }
  }
    
  def num: Parser[E] = """\d+""".r ^^ { 
    case a => {
     // println("num: " + a)
      new Var(a,i)//TODO: check
    }
  }
  
  def number: Parser[Int] = """\d+""".r ^^ { _.toInt }
  
  def term: Parser[E] = (negTerm | func | num | variable) 
  
  def negTerm: Parser[E] = "(~ " ~ term ~ ")" ^^{
    case ~(~(_,t),_) => {
      t
    }
  }
    
  def variable: Parser[E] = name ^^ {
    case s => {
      varMap.getOrElseUpdate(s,new Var(s.toString,o))
      exprMap.getOrElseUpdate(s,new Var(s.toString,o))
    }
  }
    
   def str: Parser[String] = """[^ ():]+""".r ^^ {
  
      case s => {
        //println("str: " + s)
        s
      }
    }
    
   def name: Parser[String] = "[a-zA-Z0-9]+".r ^^ {
      case s => {
      //  println("name: " + s)
        s
      }
    }
    
}
