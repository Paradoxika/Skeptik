package at.logic.skeptik.parser

import at.logic.skeptik.parser.TPTPParsers._

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

    val problem3 = ProblemParserTFFTPTP.problem("examples/problems/TFF/TFF.tffp")
    println(problem3)
    ProblemParserTFFTPTP.resetVarsSeen()
    println("\n\n\n")

    val problem4 = ProblemParserTFFTPTP.problem("examples/problems/TFF/TFA.tfap")
    println(problem4)
    ProblemParserTFFTPTP.resetVarsSeen()
    println("\n\n\n")

    val problem5 = ProblemParserTFFTPTP.problem("examples/problems/TFF/TFFBigTest.tffp")
    println(problem5)
    ProblemParserTFFTPTP.resetVarsSeen()
    println("\n\n\n")

    val problem6 = ProblemParserTHFTPTP.problem("examples/problems/THF/THF.thfp")
    println(problem6)
    ProblemParserTHFTPTP.resetVarsSeen()
    println("\n\n\n")

    val problem7 = ProblemParserTHFTPTP.problem("examples/problems/THF/LCL633^1.thfp")
    println(problem7)
    ProblemParserTHFTPTP.resetVarsSeen()
    println("\n\n\n")

    val proof1 = ProofParserCNFTPTP.read("examples/proofs/TPTP/complexCNF.tptp")
    println(proof1)
    println(ProofParserCNFTPTP.getVariables)
  }
}