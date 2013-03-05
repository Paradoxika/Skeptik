package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{CutIC, Axiom}
import at.logic.skeptik.expression.formula.{Neg}
import at.logic.skeptik.expression.{E,Var,o}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

object ProofParserVeriT extends VeriTParsers {
  def parse(fileReader: FileReader) : Proof[Node] = {
    parse(proof, fileReader) match {
      case Success(p,_) => p // returns proof whose root is in the last line of the proof file
      case Failure(message,_) => throw new Exception("Failure: " + message)
      case Error(message,_) => throw new Exception("Error: " + message)
    }
  }
}

trait VeriTParsers
extends JavaTokenParsers with RegexParsers {
  
  private var proofMap = new MMap[String,Node]
  private var exprMap = new MMap[String,E]

  def proof: Parser[Proof[Node]] = nodes ^^ { list => 
    val p = Proof(list.last)
    proofMap = new MMap[String,Node]
    exprMap = new MMap[String,E]
    p
  }
  def nodes: Parser[List[Node]] = rep(line)
  def line: Parser[Node] = "(set"  ~> name ~ "(" ~ inference <~ "))" ^^ {
    case ~(~(n, _), p) => proofMap+= ((n )-> p); p
    case x => throw new Exception("Wrong line " + x)
  }

  def inference: Parser[Node] = (resolution | input)
  def resolution: Parser[Node] = "resolution" ~> clauses <~ conclusion ^^ {(
    list => list.tail.foldLeft(list.head) { ((left, right) => CutIC(left, right)) })
  }
  def input: Parser[Node] = name ~> opt(clauses) ~> conclusion ^^ {(
    list => new Axiom(list))
  }

  def clauses: Parser[List[Node]] = ":clauses (" ~> rep(name) <~ ")" ^^ {(
    list => list.map(proofMap))
  }
  def conclusion: Parser[List[E]] = ":conclusion (" ~> rep(expression) <~ ")"

  def expression: Parser[E] = (assignmentE | simpleE)
  def assignmentE: Parser[E] = name<~ ":" <~ simpleE ^^ {(
    n => exprMap.getOrElseUpdate(n, Var(n, o)))
  }
  def simpleE: Parser[E] = (posE | negE | otherE)
  def posE: Parser[E] = name ^^ {
    n => exprMap.getOrElseUpdate(n, Var(n,o))
  }
  def negE: Parser[E] = "(not" ~> expression <~ ")" ^^ {(
    e => Neg(e))
  }
  def otherE: Parser[E] = "(" ~> otherOther ~ rep(otherOther) <~ ")" ^^ {
    case ~(op, l) => Var(l.foldLeft(op) { ((left,right) => left + right) }, o)
  }
  def otherOther: Parser[String] = ( expression ^^ (_.toString) | name )

  def name: Parser[String] = """[^ ():]+""".r
}
