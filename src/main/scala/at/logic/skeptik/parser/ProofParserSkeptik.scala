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


object ProofParserSkeptik extends ProofCombinatorParser[Node] with SkeptikParsers

trait SkeptikParsers
extends JavaTokenParsers with RegexParsers {
  
  private var proofMap = new MMap[String,Node]
  private var exprMap = new MMap[Int,E]

  def reset() = {
    proofMap = new MMap[String,Node]
    exprMap = new MMap[Int,E]
  }
  
  def proof: Parser[Proof[Node]] = rep1(line) ^^ { list => 
    Proof(list.last)
  }
  
  def line: Parser[Node] = proofName ~ "=" ~ subproof ^^ {
    case ~(~(n, _), p) => proofMap += (n -> p); p
    case wl => throw new Exception("Wrong line " + wl)
  }

  def subproof: Parser[Node] = (resolutionTree | axiom | unchecked)
  
  def resolutionTree: Parser[Node] = resolution <~ opt(conclusion)
  def subTree: Parser[Node] = (namedProof | axiom | resolution)
  def resolution: Parser[Node] = "(" ~> subTree ~ pivot ~ subTree <~ ")" ^^ {
    case ~(~(left,Some(p)),right) => R(left, right, p)
    case ~(~(left,None),   right) => R(left, right)
  }
  def pivot: Parser[Option[E]] = ( "[" ~> expression <~  "]" ^^ { case p => Some(p) }
                                 | "." ^^ { case _ => None } )
  
  def axiom: Parser[Node] = opt("axiom()") ~> conclusion ^^ {
    c => new Axiom(c)
  }
  def unchecked: Parser[Node] = name ~ premises ~ conclusion ^^ {
    case ~(~(name, premises), c) => new UncheckedInference(name,premises,c)
  }

  def premises: Parser[List[Node]] = "(" ~> rep(proofName) <~ ")" ^^ {
    list => list map proofMap
  }
  def conclusion: Parser[Sequent] = "{" ~> cedent ~ "⊢" ~ cedent <~ "}" ^^ {
    case ~(~(ant,_),suc) => Sequent(ant:_*)(suc:_*)
  }
  def cedent: Parser[Seq[E]] = repsep(expression,",")
  
//  def proofName: Parser[Int] = """\d+""".r ^^ { _.toInt }
  def proofName: Parser[String] = name

  def namedProof: Parser[Node] = proofName ^^ { proofMap(_) }
  
  def expression: Parser[E] = (assignment | namedExpr | expr)
  def assignment: Parser[E] = exprName ~ ":" ~ expr ^^ {
    case ~(~(n,_),e) => exprMap += (n -> e); e
  }

  def exprName: Parser[Int] = "#" ~> """\d+""".r ^^ { _.toInt }
  
  def namedExpr: Parser[E] = exprName ^^ { exprMap(_) }
  
  def expr: Parser[E] = (variable | infixApp | app)

  // ToDo: this parser is not distinguishing formulas and terms.
  // Terms are (wrongly) given type o.
  // As long as theory inferences are parsed as UncheckedInferences,
  // this will not be a problem.
  // Let expressions are not supported yet.
  
  def variable: Parser[E] = name ^^ { Var(_,o) }
 
  private val predefinedBigSymbols = Map(
    "and" -> bigAndC ,
    "or" -> bigOrC, 
    "∧" -> bigAndC ,
    "∨" -> bigOrC 
  )
    
  private val predefinedSymbols = Map(
    "imp" -> impC ,
    "not" -> negC ,
    "=" -> eqC(o)
  ) 
  
  def infixApp: Parser[E] = "(" ~> expression ~ name ~ expression <~ ")" ^^ {
    case ~(~(left,functionSymbol),right) => {
      val function = predefinedBigSymbols.get(functionSymbol) match {
        case None => predefinedSymbols.get(functionSymbol) match {
          case None => Var(functionSymbol, left.t -> (right.t -> o))
          case Some(c) => c
        }
        case Some(c) => c(2)
      } 
      App(App(function,left),right)
    }
  }
  
  def app: Parser[E] = "(" ~> name ~ rep(expression) <~ ")" ^^ {
    case ~(functionSymbol, args) => {
      val function = predefinedBigSymbols.get(functionSymbol) match {
        case None => predefinedSymbols.get(functionSymbol) match {
          case None => Var(functionSymbol, (args :\ (o: T)) {(a, t) => (o -> t)})
          case Some(c) => c
        }
        case Some(c) => c(args.length)
      } 
      ((function: E) /: args)((e,a) => App(e,a))
    }
  } 
  
  def name: Parser[String] = """[^ (){}:⊢,.=]+""".r
}
