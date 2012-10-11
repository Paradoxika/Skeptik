package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import java.io.FileReader
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

class SimplePropositionalResolutionProofNodeFormatParser(filename: String) 
extends JavaTokenParsers with RegexParsers {
  
  private val map = new MMap[String,SequentProofNode]

  def proof: Parser[List[(String,SequentProofNode)]] = rep(line)
  def line: Parser[(String,SequentProofNode)] = proofName ~ "=" ~ subproof ^^ {
    case ~(~(name,_),p) => map += (name -> p); (name,p)
  }
  def subproof: Parser[SequentProofNode] = (input | resolvent | leftChain | proofName) ^^ {
    case p: SequentProofNode => p
    case name: String => map(name)
  }
  def input: Parser[SequentProofNode] = "{" ~> repsep(literal,",") <~ "}" ^^ {
    list => new Axiom(Sequent(list))
  }
  def resolvent: Parser[SequentProofNode] = "(" ~> subproof ~ "." ~ subproof <~ ")" ^^ {
    case ~(~(left,_),right) => CutIC(left,right)
  }
  def leftChain: Parser[SequentProofNode] = "L(" ~> repsep(subproof, ".") <~ ")" ^^ {
    list => (list.head /: list.tail)(
      (p1,p2) => CutIC(p1,p2)
    )
  }
  def literal: Parser[E] = opt("-")~atom ^^ {
    case ~(Some(_),a) => Neg(a)
    case ~(None,a) => a
  }
  def proofName: Parser[String] = """\w+""".r
  def atom: Parser[Var] =  """\w+""".r ^^ {s => Var(s,o)}

  def getProofNode = {
    parse(proof, new FileReader(filename)) match {
      case Success(list,_) => Proof(list.last._2) // returns proof whose root is in the last line of the proof file
      case Failure(message,_) => throw new Exception(message)
      case Error(message,_) => throw new Exception(message)
    }
  }
}
