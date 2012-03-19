package ResK.parsers

import scala.util.parsing.combinator._
import scala.collection.mutable.{HashMap => MMap}
import java.io.FileReader
import ResK.proofs._
import ResK.formulas._
import ResK.expressions._
import ResK.judgments._

class SimplePropositionalResolutionProofFormatParser(filename: String) extends JavaTokenParsers with RegexParsers {
  
  private val map = new MMap[Int,SequentProof]
  private var root : SequentProof = null

  def proof: Parser[Any] = rep(line)
  def line: Parser[(Any,SequentProof)] = ("qed" | proofName) ~ "=" ~ subproof ^^ {
    case ~(~("qed",_),p) => {root = p; ("qed",p)}
    case ~(~(name,_),p) => {
        //if (name.asInstanceOf[Int]%10000 == 1) println(name.asInstanceOf[Int])
        map += (name.asInstanceOf[Int] -> p); (name,p)
      }
  }
  def subproof: Parser[SequentProof] = (input | resolvent | leftChain | proofName) ^^ {
    case p: SequentProof => p
    case name: Int => map(name)
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
  def proofName: Parser[Int] = wholeNumber ^^ {s => s.toInt}
  def atom: Parser[Var] = wholeNumber ^^ {s => Var(s,o)}

  def getProof = {
    parse(proof, new FileReader(filename))
    root
  }
}
