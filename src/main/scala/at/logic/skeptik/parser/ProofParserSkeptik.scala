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


object ProofParserSkeptik extends ProofParser[Node] with VeriTParsers

trait SkeptikParsers
extends JavaTokenParsers with RegexParsers {

  private var proofMap = new MMap[String,Node]
  private var exprMap = new MMap[String,E]

  def proof: Parser[Proof[Node]] = rep(line) ^^ { list => 
    val p = Proof(list.last)
    proofMap = new MMap[String,Node]
    exprMap = new MMap[String,E]
    p
  }
  def line: Parser[Node] = proofName ~ "=" ~ subproof ^^ {
    case ~(~(n, _), p) => proofMap += (n -> p); p
    case x => throw new Exception("Wrong line " + x)
  }
  def subproof: Parser[Node] = (input | resolvent | leftChain | proofName) ^^ {
    case p: Node => p
    case name: String => proofMap(name)
  }
  def input: Parser[Node] = "{" ~> repsep(literal,",") <~ "}" ^^ {
    list => new Axiom(list)
  }
  def resolvent: Parser[Node] = "(" ~> subproof ~ "." ~ subproof <~ ")" ^^ {
    case ~(~(left,_),right) => CutIC(left,right)
  }
  def leftChain: Parser[Node] = "L(" ~> repsep(subproof, ".") <~ ")" ^^ {
    list => (list.head /: list.tail) (
      (p1,p2) => CutIC(p1,p2)
    )
  }
  def literal: Parser[E] = opt("-")~atom ^^ {
    case ~(Some(_),a) => Neg(a)
    case ~(None,a) => a
  }
  def proofName: Parser[String] = """\w+""".r
  def atom: Parser[Var] =  """\w+""".r ^^ {s => Var(s,o)}
}
