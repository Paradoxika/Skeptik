package at.logic.skeptik.parser

import at.logic.skeptik.parser.TPTPParsers.{ProblemParserCNFTPTP, ProblemParserFOFTPTP, ProofParserCNFTPTP}

object TPTPTest {
  def main(args: Array[String]):Unit = {
    val problem1 = ProblemParserCNFTPTP.problem("examples/problems/CNF/CNF.cnfp")
    println(problem1)
    ProblemParserCNFTPTP.resetVarsSeen()
    println("\n\n\n")
    val problem2 = ProblemParserFOFTPTP.problem("examples/problems/FOF/FOF.fofp")
    println(problem2)
    ProblemParserFOFTPTP.resetVarsSeen()
    println("\n\n\n")
    val proof1 = ProofParserCNFTPTP.read("examples/proofs/TPTP/complexCNF.tptp")
    println(proof1)
    println(ProofParserCNFTPTP.getVariables)
  }
}