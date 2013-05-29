package at.logic.skeptik.parser

import scala.util.parsing.combinator._

import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.algorithm.compressor.algorithms

object AlgorithmParser extends RegexParsers {
  type P = Proof[N]
  type A = P => P
  
  //def algorithms: Parser[List[A]] = repsep(algorithm,",") 
  
  def algo : Parser[A] = (atomicAlgo | composedAlgo)
  
  def atomicAlgo : Parser[A] = """[a-zA-Z0-9]+""".r flatMap { name => 
    algorithms.get(name) match {
      case Some(a) => success(a)
      case None => failure("There is no algorithm with name + '" + name + "'")
    }
  }
  
  def composedAlgo : Parser[A] = "(" ~> repsep(algo, ".") <~ ")" ^^ {
    case Nil => (p: P) => p  // an empty composition of algorithms is the identity algorithm
    case h::Nil => h
    case h::t =>  (h /: t) { (acc, next) => acc compose next }
  }
  
  def parse(s: String) : A = {
    parse(algo, s) match {
      case Success(a,_) => a // returns proof whose root is in the last line of the proof file
      case Failure(message,_) => throw new Exception("Failure: " + message)
      case Error(message,_) => throw new Exception("Error: " + message)
    }
  }

}