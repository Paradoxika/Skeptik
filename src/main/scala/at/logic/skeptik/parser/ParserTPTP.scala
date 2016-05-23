package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

/**
  * This modules describe the TPTP syntax as descrobed in
  * www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html
  *
  * The non terminals don't follow camelcase convention to
  * reflect the grammar in a more natural way.
  *
  * @author Ezequiel Postan
  * @since 23.05.2016
  */

class UnexpectedEmptyTPTPFileException extends Exception("Unexpected Empty File")

object ProofParserTPTP   extends ProofCombinatorParser[Node] with ProofParserTPTP
object ProblemParserTPTP extends ProblemParserTPTP

/**
  * The BaseParserTPTP implements the common parsers shared both
  * by problems and proof objects described by the TPTP syntax
  */
trait BaseParserTPTP
extends JavaTokenParsers with PackratParsers {

  def fof_annotated = "fof" ~ "(" ~ name ~ "," ~ formula_role ~ "," ~ fof_logic_formula ~ opt(annotations) ~ ")" <~ "."
  def cnf_annotated = "cnf" ~ "(" ~ name ~ "," ~ formula_role ~ "," ~ cnf_logic_formula ~ opt(annotations) ~ ")" <~ "."
  def tff_annotated = "tff" ~ "(" ~ name ~ "," ~ formula_role ~ "," ~ tff_logic_formula ~ opt(annotations) ~ ")" <~ "."
  def thf_annotated = "thf" ~ "(" ~ name ~ "," ~ formula_role ~ "," ~ thf_logic_formula ~ opt(annotations) ~ ")" <~ "."
  def tpi_annotated = "tpi" ~ "(" ~ name ~ "," ~ formula_role ~ "," ~ tpi_logic_formula ~ opt(annotations) ~ ")" <~ "."
  def tpi_logic_formula = fof_logic_formula


  def fof_logic_formula = ???
  def cnf_logic_formula = ???
  def tff_logic_formula = ???
  def thf_logic_formula = ???

  def annotations  : PackratParser[String] = ???

  def name         : PackratParser[String] = atomic_word | wholeNumber
  def formula_role : PackratParser[String] = "axiom" | "hypothesis" | "definition" | "assumption" |
                                             "lemma" | "theorem" | "corollary" | "conjecture" |
                                             "negated_conjecture" | "plain" | "type" | "fi_domain" |
                                             "fi_functors" | "fi_predicates" | "unknown"

  def atomic_word   : PackratParser[String] = lower_word | single_quoted
  def lower_word    : PackratParser[String] = regex("[a-z][a-zA-Z0-9_]*".r)
  def single_quoted : PackratParser[String] = """'[^']*'""".r ^^ { _.drop(1).dropRight(1) }

  def comments = ???

}

trait ProblemParserTPTP
extends BaseParserTPTP {
}

trait ProofParserTPTP
extends BaseParserTPTP {

  private var varMap   = new MMap[String,E]
  private var exprMap  = new MMap[String,E]
  private var proofMap = new MMap[String,Node]

  def reset() : Unit = {
    varMap.clear()
    exprMap.clear()
    proofMap.clear()
  }

  //returns the actual proof
  def proof: Parser[Proof[Node]] = TPTP_file ^^ {p => if (p.nonEmpty) p.last
                                                      else throw new UnexpectedEmptyTPTPFileException
                                                }

  def TPTP_file  : PackratParser[List[Proof[Node]]] = rep(TPTP_input)
  def TPTP_input : PackratParser[Proof[Node]] = annotated_formula | include

  def include  = ???

  def annotated_formula : PackratParser[Proof[Node]] = ???

  /*
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
  */
}
