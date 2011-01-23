/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import scala.util.parsing.combinator._
import proofCompression.ResolutionCalculus._
import scala.collection.mutable._
import java.io.FileReader

object ProofParser extends JavaTokenParsers with RegexParsers {
  private var map = new HashMap[Int,Proof]
  private var root : Proof = null

  // ToDo: i CAN IMProve sharing of atom names, as I do for proofs

  def proof: Parser[Any] = rep(line)
  def line: Parser[(Any,Proof)] = ("qed" | proofName) ~ "=" ~ subproof ^^ {
    case ~(~("qed",_),p) => {println("qed"); root = p; ("qed",p)}
    case ~(~(name,_),p) => {
        if (name.asInstanceOf[Int]/1000 == 0) println(name.asInstanceOf[Int])
        map += (name.asInstanceOf[Int] -> p); (name,p)
      }
  }
  def subproof: Parser[Proof] = (input | resolvent | leftChain | proofName) ^^ {
    case p: Proof => p
    case name: Int => map(name)
  }
  def input: Parser[Proof] = "{" ~> repsep(literal,",") <~ "}" ^^ {
    list => Input(list.toSet[Literal])
  }
  def resolvent: Parser[Proof] = "(" ~> subproof ~ "." ~ subproof <~ ")" ^^ {
    case ~(~(left,_),right) => Resolvent(left,right)
  }
  def leftChain: Parser[Proof] = "L(" ~> repsep(subproof, ".") <~ ")" ^^ {
    list => (list.head /: list.tail)(
      (p1,p2) => Resolvent(p1,p2)
    )
  }
  def literal: Parser[Literal] = opt("-")~atom ^^ {
    case ~(Some(_),a) => L(a, false)
    case ~(None,a) => L(a, true)
  }
  def proofName: Parser[Int] = """[0-9]\w*""".r ^^ {s => s.toInt}
  def atom: Parser[Int] = """[0-9]\w*""".r ^^ {s => s.toInt}

  def getProofFromFile(filename: String) = {
    map = new HashMap[Int,Proof]
    parse(proof, new FileReader(filename))
    root
  }
}

//object ProofParser extends JavaTokenParsers with RegexParsers {
//  private var map = new HashMap[String,Proof]
//
//  def proof: Parser[Any] = rep(line)
//
//  def line: Parser[(String,Proof)] = proofName ~ "=" ~ subproof ^^ {
//    case ~(~(name,_),p) => {map += (name -> p); println(name); (name,p)}
//  }
//  def subproof: Parser[Proof] = (input | resolvent | proofName) ^^ {
//    case p: proofCompression.ResolutionCalculus.Input => p
//    case p: Resolvent => p
//    case name: String => map(name)
//  }
//  def input: Parser[proofCompression.ResolutionCalculus.Input] = "{" ~> repsep(literal,",") <~ "}" ^^ {
//    list => Input(list.toSet[Literal])
//  }
//  def resolvent: Parser[Resolvent] = "(" ~> subproof ~ "." ~ subproof <~ ")" ^^ {
//    case ~(~(left,_),right) => Resolvent(left,right)
//  }
//  def literal: Parser[Literal] = opt("-")~atom ^^ {
//    case ~(Some(_),lit) => L(lit, false)
//    case ~(None,lit) => L(lit, true)
//  }
//  def proofName: Parser[String] = """[a-zA-Z0-9]\w*""".r
//  def atom: Parser[String] = """[a-zA-Z0-9]\w*""".r
//
//  def getProofFromFile(filename: String) = {
//    map = new HashMap[String,Proof]
//    parse(proof, new FileReader(filename))
//    map("clempty")
//  }
//}
