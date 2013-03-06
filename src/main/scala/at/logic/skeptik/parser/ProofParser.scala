package at.logic.skeptik.parser

import scala.util.parsing.combinator._

import java.io.FileReader
import at.logic.skeptik.proof.{Proof,ProofNode}

abstract class ProofParser[N <: ProofNode[_,N]] extends RegexParsers {
  def proof : Parser[Proof[N]]
  
  def read(filename: String) : Proof[N] = {
    parse(proof, new FileReader(filename)) match {
      case Success(p,_) => p // returns proof whose root is in the last line of the proof file
      case Failure(message,_) => throw new Exception("Failure: " + message)
      case Error(message,_) => throw new Exception("Error: " + message)
    }
  }
}