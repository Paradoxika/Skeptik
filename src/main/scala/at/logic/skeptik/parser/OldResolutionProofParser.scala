package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import java.io.FileReader


object ProofParser extends JavaTokenParsers with RegexParsers {
  import at.logic.skeptik.proof.oldResolution._
  import at.logic.skeptik.proof.oldResolution.typeAliases._
  private var map = new MMap[Int,Proof]
  private var root : Proof = null

  def proof: Parser[Any] = rep(line)
  def line: Parser[(Any,Proof)] = ("qed" | proofName) ~ "=" ~ subproof ^^ {
    case ~(~("qed",_),p) => {println("qed"); root = p; ("qed",p)}
    case ~(~(name,_),p) => {
        if (name.asInstanceOf[Int]%10000 == 1) println(name.asInstanceOf[Int])
        map += (name.asInstanceOf[Int] -> p); (name,p)
      }
  }
  def subproof: Parser[Proof] = (input | resolvent | leftChain | proofName) ^^ {
    case p: Proof => p
    case name: Int => map(name)
  }
  def input: Parser[Proof] = "{" ~> repsep(literal,",") <~ "}" ^^ {
    list => new at.logic.skeptik.proof.oldResolution.Input(list.toSet[Literal])
  }
  def resolvent: Parser[Proof] = "(" ~> subproof ~ "." ~ subproof <~ ")" ^^ {
    case ~(~(left,_),right) => new Resolvent(left,right)
  }
  def leftChain: Parser[Proof] = "L(" ~> repsep(subproof, ".") <~ ")" ^^ {
    list => (list.head /: list.tail)(
      (p1,p2) => new Resolvent(p1,p2)
    )
  }

  def literal: Parser[Literal] = opt("-")~atom ^^ {
    case ~(Some(_),a) => L(a, false)
    case ~(None,a) => L(a, true)
  }

  def proofName: Parser[Int] = wholeNumber ^^ {s => s.toInt}
  def atom: Parser[Atom] = wholeNumber ^^ {s => s.toInt}

  def getProofFromFile(filename: String) = {
    map = new MMap[Int,Proof]
    parse(proof, new FileReader(filename))
    root
  }
}
