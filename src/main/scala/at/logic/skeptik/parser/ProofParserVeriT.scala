package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap, HashSet => MSet}
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import at.logic.skeptik.proof.sequent.lk.{TheoryR, TheoryLemma, EqCongruent,EqTransitive,EqReflexive,EqSymmetric}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.ArrayBuffer

object ProofParserVeriT extends ProofCombinatorParser[Node] with VeriTParsers

trait VeriTParsers
extends JavaTokenParsers with RegexParsers {
  
//  private var proofMap = new MMap[Int,Node]
  private val proofArray = new ArrayBuffer[Node]()
  private var exprMap = new MMap[Int,E]
  private var bindMap = new MMap[String,E]
  
  def reset() = {
    proofArray.clear
    exprMap = new MMap[Int,E]
    bindMap = new MMap[String,E]
  }
  

  def proof: Parser[Proof[Node]] = rep(line) ^^ { list => 
    Proof(list.last)
  }
  
  def line: Parser[Node] = "(set"  ~> proofName ~ "(" ~ inference <~ "))" ^^ {
    case ~(~(n, _), p) => {
//      proofMap += (n -> p); p
      proofArray += p
      p
    }
    case wl => throw new Exception("Wrong line " + wl)
  }
  
  // A convenient method for creating left associative chains of inferences
  def createChain(premises: List[Node])( infer: (Node, Node) => Node ) = {
    (premises.head /: premises.tail) { (left, right) => 
      try { infer(left, right) }
      catch {case e: Exception => throw(e) }
    }
  }
  
  def inference: Parser[Node] = (resolution | axiom | theory | unchecked)
  
  def resolution: Parser[Node] = "resolution" ~> premises <~ conclusion ^^ 
    (createChain(_)((l, r) => R(l, r)))
  
  def theory: Parser[Node] = (eq_axiom | th_lemma | th_resolution)
  
  def eq_axiom: Parser[Node] = (eq_congruent | eq_reflexive | eq_transitive )
  
  def eq_congruent: Parser[Node] = "eq_congruent" ~> conclusion ^^ {
    list => EqCongruent(list)
  }
 
  def eq_symmetric: Parser[Node] = "eq_symmetric" ~> conclusion ^^ {
    list => EqSymmetric(list)
  }
  
  def eq_reflexive: Parser[Node] = "eq_reflexive" ~> conclusion ^^ {
    list => EqReflexive(list)
  }
  
  def eq_transitive: Parser[Node] = "eq_transitive" ~> conclusion ^^ {
    list => EqTransitive(list)
  }
  
  def th_lemma: Parser[Node] = "th_lemma" ~> conclusion ^^ {
    list => TheoryLemma(list)
  }
  
  def th_resolution: Parser[Node] = "th_resolution" ~> premises <~ conclusion ^^ 
    (createChain(_)((l, r) => TheoryR(l, r)))
  
  def axiom: Parser[Node] = "input" ~> conclusion ^^ {
    list => new Axiom(list)
  }
  def unchecked: Parser[Node] = name ~ opt(premises) ~ opt(args) ~ conclusion ^^ {
    case ~(~(~(name, None),_), list) => new UncheckedInference(name,Seq(),list)
    case ~(~(~(name, Some(premises)),_), list) => new UncheckedInference(name,premises,list)
  }

  def premises: Parser[List[Node]] = ":clauses (" ~> rep(proofName) <~ ")" ^^ {
    list => list map {pn => proofArray(pn - 1)}
//    list => list map proofMap
  }

  def args: Parser[List[Int]] = ":iargs (" ~> rep("""\d+""".r) <~ ")" ^^ {
    list => list map { _.toInt }
  }
  def conclusion: Parser[List[E]] = ":conclusion (" ~> rep(expression) <~ ")"


  def proofName: Parser[Int] = ".c" ~> """\d+""".r ^^ { _.toInt }
  
  def expression: Parser[E] = (assignment | namedExpr | expr)
  
  def assignment: Parser[E] = exprName ~ ":" ~ expr ^^ {
    case ~(~(n,_),e) => {
      exprMap += (n -> e); e
    }
  }

  def exprName: Parser[Int] = "#" ~> """\d+""".r ^^ { _.toInt }
  
  def namedExpr: Parser[E] = exprName ^^ { exprMap(_) }
  
  def expr: Parser[E] = (variable | app | let)

  def let: Parser[E] = "(" ~> "let" ~> "(" ~> rep(binding) ~> ")" ~> expression <~ ")" ^^ { e =>
    bindMap = new MMap[String,E]
    e
  }

  def binding: Parser[Any] = "(" ~> name ~ expression <~ ")" ^^ {
    case ~(sym, exp) => bindMap += (sym -> exp) ; ()
  }

  // ToDo: this parser is not distinguishing formulas and terms.
  // Terms are (wrongly) given type o.
  // As long as theory inferences are parsed as UncheckedInferences,
  // this will not be a problem.
  
  def variable: Parser[E] = name ^^ { v => bindMap.getOrElse(v, Var(v,o)) }
 
  private val predefinedBigSymbols = Map(
    "and" -> bigAndC ,
    "or" -> bigOrC 
  )
    
  private val predefinedSymbols = Map(
    "imp" -> impC ,
    "not" -> negC ,
    "=" -> eqC(o)
  ) 
  
 private val equalitySymbols = Map(
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
