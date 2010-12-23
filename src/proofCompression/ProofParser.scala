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
  private var map = new HashMap[String,ResolutionProof]

  def proof: Parser[Any] = rep(line)
  def line: Parser[(String,ResolutionProof)] = proofName ~ "=" ~ subproof ^^ {
    case ~(~(name,_),p) => {map += (name -> p); (name,p)}
  }
  def subproof: Parser[ResolutionProof] = (input | resolvent | proofName) ^^ {
    case p: proofCompression.ResolutionCalculus.Input => p
    case p: Resolvent => p
    case name: String => map(name)
  }
  def input: Parser[proofCompression.ResolutionCalculus.Input] = "{" ~> repsep(literal,",") <~ "}" ^^ {
    list => Input(list.toSet[Literal])
  }
  def resolvent: Parser[Resolvent] = "(" ~> subproof ~ "." ~ subproof <~ ")" ^^ {
    case ~(~(left,_),right) => Resolvent(left,right)
  }
  def literal: Parser[Literal] = opt("-")~atom ^^ {
    case ~(Some(_),lit) => L(lit, false)
    case ~(None,lit) => L(lit, true)
  }
  def proofName: Parser[String] = """[a-zA-Z0-9]\w*""".r
  def atom: Parser[String] = """[a-zA-Z0-9]\w*""".r

  def getProofFromFile(filename: String) = {
    map = new HashMap[String,ResolutionProof]
    parse(proof, new FileReader(filename))
    map("clempty")
  }
}
