package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{CutIC, Axiom, UncheckedInference}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

object ProofParserVeriT extends ProofParser[Node] with VeriTParsers

trait VeriTParsers
extends JavaTokenParsers with RegexParsers {
  
  private var proofMap = new MMap[Int,Node]
  private var exprMap = new MMap[Int,E]

  def proof: Parser[Proof[Node]] = rep(line) ^^ { list => 
    val p = Proof(list.last)
    proofMap = new MMap[Int,Node]
    exprMap = new MMap[Int,E]
    p
  }
  def line: Parser[Node] = "(set"  ~> proofName ~ "(" ~ inference <~ "))" ^^ {
    case ~(~(n, _), p) => proofMap += (n -> p); p
    case wl => throw new Exception("Wrong line " + wl)
  }

  def inference: Parser[Node] = (resolution | axiom | unchecked)
  def resolution: Parser[Node] = "resolution" ~> premises <~ conclusion ^^ {
    list => (list.head /: list.tail) { ((left, right) => CutIC(left, right)) }
  }
  def axiom: Parser[Node] = "input" ~> conclusion ^^ {
    list => new Axiom(list)
  }
  def unchecked: Parser[Node] = name ~ opt(premises) ~ conclusion ^^ {
    case ~(~(name, None), list) => new UncheckedInference(name,Seq(),list)
    case ~(~(name, Some(premises)), list) => new UncheckedInference(name,premises,list)
  }

  def premises: Parser[List[Node]] = ":clauses (" ~> rep(proofName) <~ ")" ^^ {
    list => list map proofMap
  }
  def conclusion: Parser[List[E]] = ":conclusion (" ~> rep(expression) <~ ")"

  def proofName: Parser[Int] = ".c" ~> """\d+""".r ^^ { _.toInt }
  
//  def expression: Parser[E] = (assignmentE | simpleE)
//  def assignmentE: Parser[E] = name<~ ":" <~ simpleE ^^ {
//    n => exprMap.getOrElseUpdate(n, Var(n, o))
//  }
//  def simpleE: Parser[E] = (posE | negE | otherE)
//  def posE: Parser[E] = name ^^ {
//    n => exprMap.getOrElseUpdate(n, Var(n,o))
//  }
//  def negE: Parser[E] = "(not" ~> expression <~ ")" ^^ {
//    e => Neg(e)
//  }
//  def otherE: Parser[E] = "(" ~> otherOther ~ rep(otherOther) <~ ")" ^^ {
//    case ~(op, l) => Var(l.foldLeft(op) { ((left,right) => left + right) }, o)
//  }
//  def otherOther: Parser[String] = ( expression ^^ (_.toString) | name )


  
  def expression: Parser[E] = (assignment | namedExpr | expr)
  def assignment: Parser[E] = exprName ~ ":" ~ expr ^^ {
    case ~(~(n,_),e) => exprMap += (n -> e); e
  }

  def exprName: Parser[Int] = "#" ~> """\d+""".r ^^ { _.toInt }
  
  def namedExpr: Parser[E] = exprName ^^ { exprMap(_) }
  
  def expr: Parser[E] = (variable | app)

  // ToDo: this parser is not distinguishing formulas and terms.
  // Terms are (wrongly) given type o.
  // As long as theory inferences are parsed as UncheckedInferences,
  // this will not be a problem.
  // Let expressions are not supported yet.
  
  def variable: Parser[E] = name ^^ { Var(_,o) }
 
  private val predefinedBigSymbols = Map(
    "and" -> bigAndC ,
    "or" -> bigOrC 
  )
    
  private val predefinedSymbols = Map(
    "imp" -> impC ,
    "not" -> negC ,
    "=" -> eqC(o)
  ) 
  
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
  
  def name: Parser[String] = """[^ ():]+""".r
}
