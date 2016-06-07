package at.logic.skeptik.parser

import at.logic.skeptik.parser.TPTPParsers.{ProblemParserCNFTPTP, ProblemParserFOFTPTP}

object TPTPTest {
  def main(args: Array[String]):Unit = {
    val problem1 = ProblemParserCNFTPTP.problem("examples/problems/CNF/CNF.cnfp")
    println(problem1)
    println("\n\n\n")
    val problem2 = ProblemParserFOFTPTP.problem("examples/problems/FOF/FOF.fofp")
    println(problem2)
  }
}