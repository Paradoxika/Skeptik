package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.algorithm.compressor.Timeout
import at.logic.skeptik.expression.Var
import at.logic.skeptik.parser.TPTPParsers.ProofParserCNFTPTP

import scala.collection.mutable.{Set => MSet}


object FOCottonSplitTest {
  def main(args: Array[String]): Unit = {
    val proof = ProofParserCNFTPTP.read("examples/proofs/TPTP/FOSplitToCompress.tptp")
    val variables = ProofParserCNFTPTP.getVariables
    println("Original Proof:")
    print("Variables: ")
    println(variables.mkString(","))
    println("Proof:")
    println(proof)
    val split = new FOCottonSplit(variables, 1000)
    println(split(proof))
  }
}

/**
  * Created by eze on 2016.06.14..
  */
class FOCottonSplit(override val variables : MSet[Var], val timeout: Int)
extends FOSplit(variables) with FOAdditivityHeuristic with FORandomChoice with Timeout with SeenLiteralsHeuristic with NameEquality
