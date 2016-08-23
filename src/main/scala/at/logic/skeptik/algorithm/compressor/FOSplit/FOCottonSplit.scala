package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.algorithm.compressor.Timeout
import at.logic.skeptik.expression.Var
import at.logic.skeptik.parser.TPTPParsers.ProofParserCNFTPTP

import scala.collection.mutable.{Set => MSet}


object FOCottonSplitTest {
  def main(args: Array[String]): Unit = {
    val proof     = ProofParserCNFTPTP.read("examples/proofs/TPTP/FOSplitToCompress.tptp")
    val variables = ProofParserCNFTPTP.getVariables
    val split     = new FOCottonSplit(variables, 100)
    println("Original Proof:")
    print("Variables: ")
    println(variables.mkString(","))
    println("Proof:")
    println(proof)
    println(split(proof))
  }
}

/**
  * The class FOCottonSplit represent a first order generalization of
  * Cotton's splitting algorithm.
  *
  * @param variables The set of variables that appear in the proof
  * @param timeout   A timeout parameter to stop the iterative splitting steps
  */
class FOCottonSplit(override val variables : MSet[Var], val timeout: Int)
extends FOSplit(variables) with FOAdditivityHeuristic with FOHighestAdditivityChoice with Timeout
  with SetContentionAndSeenLiteralsHeuristic with NameEquality
