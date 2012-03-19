package ResK.calculi

import scala.util.parsing.combinator._
import scala.collection.mutable.{HashMap => MMap}
import java.io.FileReader


object ProofParser extends JavaTokenParsers with RegexParsers {
  import ResK.calculi.resolution._
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
    list => new ResK.calculi.resolution.Input(list.toSet[Literal])
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

object ProofParserNew extends JavaTokenParsers with RegexParsers {
  import ResK.proofs._
  import ResK.formulas._
  import ResK.expressions._
  import ResK.judgments._
  
  private var map = new MMap[Int,SequentProof]
  private var root : SequentProof = null

  def proof: Parser[Any] = rep(line)
  def line: Parser[(Any,SequentProof)] = ("qed" | proofName) ~ "=" ~ subproof ^^ {
    case ~(~("qed",_),p) => {println("qed"); root = p; ("qed",p)}
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

  def getProofFromFile(filename: String) = {
    map = new MMap[Int,SequentProof]
    parse(proof, new FileReader(filename))
    root
  }
}
