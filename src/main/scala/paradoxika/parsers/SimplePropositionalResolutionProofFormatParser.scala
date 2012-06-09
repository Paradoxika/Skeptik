package ResK.parsers

import scala.util.parsing.combinator._
import scala.collection.mutable.{HashMap => MMap}
import java.io.FileReader
import ResK.proofs._
import ResK.formulas._
import ResK.expressions._
import ResK.judgments._

class SimplePropositionalResolutionProofFormatParser(filename: String) 
extends JavaTokenParsers with RegexParsers {
  
  private val map = new MMap[String,SequentProof]

  def proof: Parser[List[(String,SequentProof)]] = rep(line)
  def line: Parser[(String,SequentProof)] = proofName ~ "=" ~ subproof ^^ {
    case ~(~(name,_),p) => map += (name -> p); (name,p)
  }
  def subproof: Parser[SequentProof] = (input | resolvent | leftChain | proofName) ^^ {
    case p: SequentProof => p
    case name: String => map(name)
  }
  def input: Parser[SequentProof] = "{" ~> repsep(literal,",") <~ "}" ^^ {
    list => new Axiom(Sequent(list))
  }
  def resolvent: Parser[SequentProof] = "(" ~> subproof ~ "." ~ subproof <~ ")" ^^ {
    case ~(~(left,_),right) => CutIC(left,right)
  }
  def leftChain: Parser[SequentProof] = "L(" ~> repsep(subproof, ".") <~ ")" ^^ {
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

  def getProof = {
    parse(proof, new FileReader(filename)) match {
      case Success(list,_) => list.last._2 // returns proof whose root is in the last line of the proof file
      case Failure(message,_) => throw new Exception(message)
      case Error(message,_) => throw new Exception(message)
    }
  }
}
