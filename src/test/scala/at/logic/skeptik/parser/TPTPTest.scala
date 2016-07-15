package at.logic.skeptik.parser

import java.io.PrintWriter

import at.logic.skeptik.parser.TPTPParsers.TPTPAST.{IncludeDirective, TPTPDirective}
import at.logic.skeptik.parser.TPTPParsers.TPTPTokens
import at.logic.skeptik.parser.TPTPParsers._

import scala.collection.mutable
import scala.collection.mutable.HashSet
import scala.io.Source

object TPTPTest {
  def main(args: Array[String]):Unit = {
    val problem1 = ProblemParserFOFTPTP.problem("examples/problems/FOF/AGT001+1.fofp")
    println(problem1)
    ProblemParserFOFTPTP.resetVarsSeen()

    /*
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
    */
  }
}

// This test uses local files not included in the project. It was used to test the parsers over most
// parts of the TPTP problem library. If you need to run this test feel free to contact Ezequiel Postan
// at ezequiel_postan [at] hotmail [dot] com
object TPTPExtensiveTest extends BaseParserTPTP {

  import lexical._

  /**
    * This parser is used only for tests
    *
    * @param axiomsFolderPath The path where the axioms folder of the include directives is located
    *
    * @return The parser that parse include directives appending the axiomsFolderPath to the included file name.
    */
  def TPTP_file_TESTS(axiomsFolderPath : String) : Parser[List[TPTPDirective]] = rep(TPTP_input_TESTS(axiomsFolderPath)) ^^ {List.concat(_ :_*)}
  def TPTP_input_TESTS(axiomsFolderPath : String): Parser[List[TPTPDirective]] = (annotated_formula ^^ {List(_)} | include_TESTS(axiomsFolderPath)) ^^{List.concat(_)}
  def include_TESTS(axiomsFolderPath : String) : Parser[List[TPTPDirective]] = (
    (elem(Include) ~ elem(LeftParenthesis)) ~> elem("Single quoted", _.isInstanceOf[SingleQuoted])
      ~ opt((elem(Comma) ~ elem(LeftBracket)) ~> repsep(name,elem(Comma)) <~ elem(RightBracket))
      <~ (elem(RightParenthesis) ~ elem(Dot)) ^^ {
      case SingleQuoted(fileName) ~ Some(formulas) => expandIncludes(List(IncludeDirective(axiomsFolderPath + fileName, formulas)),TPTP_file_TESTS(axiomsFolderPath))
      case SingleQuoted(fileName) ~       _        => expandIncludes(List(IncludeDirective(axiomsFolderPath + fileName, List.empty)),TPTP_file_TESTS(axiomsFolderPath))
    }
    )


  def getProblems(file: String, path: String): mutable.HashSet[String] = {
    val outTj = mutable.HashSet[String]()

    for (line <- Source.fromFile(file).getLines()) {
      val newProblemN = path + line
      outTj.add(newProblemN)
    }
    outTj
  }

  def main(args: Array[String]): Unit = {
    val problemsPath     : String = "/home/eze/Escritorio/TPTP-Parsers/problems-download/Problems/"
    val axiomsFolderPath : String = "/home/eze/Escritorio/TPTP-Parsers/problems-download/"
    val problemsList     : String = "/home/eze/Escritorio/TPTP-Parsers/problems-download/Problems/list.txt"

    val problemSet = getProblems(problemsList, problemsPath)
    val results    = new PrintWriter("results-TPTP-TFF-Parsing-2.log")

    var suc  : Int = 0
    var fail : Int = 0
    var problemStartTime = 0L
    var problemEndTime   = 0L
    var problemRunTime   = 0L
    var testStartTime = System.nanoTime

    var problemList = problemSet.toList
    problemList = problemList.sorted

    for (problem <- problemList) {
      try {
        results.print("Parsing " + problem + ": ")
        results.flush()
        problemStartTime = System.nanoTime
        extract(problem, TPTP_file_TESTS(axiomsFolderPath))
        problemEndTime = System.nanoTime
        problemRunTime = problemEndTime - problemStartTime
        results.println("SUCCEEDED in " + (problemRunTime/1000000000.0).toString + " seconds")
        suc = suc + 1
      } catch {
        case e : Throwable =>
          problemEndTime = System.nanoTime
          problemRunTime = problemEndTime - problemStartTime
          results.println(" FAILED after " + (problemRunTime/1000000000.0).toString + " seconds")
          results.println(e)
          fail = fail + 1
      }
      results.flush()
    }

    val testEndTime = System.nanoTime
    val testRunTime = testEndTime - testStartTime
    results.println("\n\nSuccess cases: " + suc.toString + "\nFailed cases: " + fail.toString + "\nTotal files tested " + (suc+fail).toString)
    results.println("The test took " + (testRunTime/1000000000.0).toString + " seconds to finish")
    results.flush()
  }
}
