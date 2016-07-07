package at.logic.skeptik.parser

import at.logic.skeptik.parser.TPTPParsers.ProblemParserFOFTPTP

object TPTPTest {
  def main(args: Array[String]):Unit = {
    val problem1 = ProblemParserFOFTPTP.problem("examples/problems/FOF/AGT001+1.fofp")
    println(problem1)
    ProblemParserFOFTPTP.resetVarsSeen()
  }
}