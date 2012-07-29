package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import java.io.FileReader
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment._
import at.logic.skeptik.expression._

class SMT2Parser(filename: String)
extends JavaTokenParsers with RegexParsers {
  
  private val proofMap = new MMap[String,SequentProof]
  private val exprMap  = new MMap[String,E]

  def proof: Parser[List[SequentProof]] = rep(line)
  def line: Parser[SequentProof] = "(set"  ~> name ~ "(" ~ inference <~ "))" ^^ {
    case ~(~(n,_),p) => proofMap += (n -> p); p
    case x => throw new Exception("Wrong line " + x)
  }

  def inference: Parser[SequentProof] = (resolution | input)
  def resolution: Parser[SequentProof] = "resolution" ~> clauses <~ conclusion ^^ {
    list => list.tail.foldLeft(list.head) { (left,right) => CutIC(left,right) }
  }
  def input: Parser[SequentProof] = name ~> opt(clauses) ~> conclusion ^^ {
    list => new Axiom(Sequent(list))
  }

  def clauses: Parser[List[SequentProof]] = ":clauses (" ~> rep(name) <~ ")" ^^ {
    list => list.map(proofMap)
  }
  def conclusion: Parser[List[E]] = ":conclusion (" ~> rep(expression) <~ ")"

  def expression: Parser[E] = (assignmentE | simpleE)
  def assignmentE: Parser[E] = name ~ ":" ~ simpleE ^^ {
    case ~(~(n,_),e) => exprMap.update(n,e) ; e
  }
  def simpleE: Parser[E] = (posE | negE | andE | orE | letE | otherE)
  def posE: Parser[E] = name ^^ {
    n => exprMap.getOrElse(n, Var(n,o))
  }
  def negE: Parser[E] = "(not" ~> expression <~ ")" ^^ {
    e => Neg(e)
  }
  def andE: Parser[E] = "(and" ~> rep(expression) <~ ")" ^^ {
    list => list.tail.foldLeft(list.head) { (left,right) => And(left,right) }
  }
  def orE: Parser[E] = "(or" ~> rep(expression) <~ ")" ^^ {
    list => list.tail.foldLeft(list.head) { (left,right) => Or(left,right) }
  }
  def otherE: Parser[E] = "(" ~> name ~ rep(expression) <~ ")" ^^ {
    case ~(op,l) => Var(l.foldLeft(op) { (left,right) => left.toString + right.toString }, o)
  }

  def letE: Parser[E] = "(let (" ~> rep(letAssignment) ~> ")" ~> expression <~ ")"
  def letAssignment: Parser[Unit] = "(" ~> name ~ expression <~ ")" ^^ {
    case ~(n,e) => exprMap.update(n,e)
  }

  def name: Parser[String] = """[^ ():]+""".r

  def getProof = {
    parse(proof, new FileReader(filename)) match {
      case Success(Nil,_) => throw new Exception(proofMap.keys.toString)
      case Success(list,_) => list.last // returns proof whose root is in the last line of the proof file
      case Failure(message,_) => throw new Exception(message)
      case Error(message,_) => throw new Exception(message)
    }
  }
}
