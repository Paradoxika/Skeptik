package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.parser.ParserException
import scala.io.Source
import at.logic.skeptik.parser.SequentParser
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.expression._
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.Contraction
import java.io.PrintWriter

object CADEExperimentDriver extends checkProofEquality {

  def getProblems(file: String, path: String): MSet[String] = {
    val outTj = MSet[String]()

    for (line <- Source.fromFile(file).getLines()) {
      val newProblemN = path + "GoodProofs\\" + line.substring(0, 3) + "\\" + line + ".spass"
      println(newProblemN)
      outTj.add(newProblemN)
    }
    outTj
  }

  def main(args: Array[String]): Unit = {
    //    val path = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\"
    //    val proofList = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\good_all.txt"

    val path = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\"
    val proofList = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\all_good_nov10.txt"
//    val problemSetS = new MSet[String]()//getProblems(proofList, path)
          val problemSetS = getProblems(proofList, path)
//val problemSetS = getProblems(proofList, path).filter(_ == "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\GRP\\GRP028-1.spass")
//    problemSetS.add("C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\GRP\\GRP028-1.spass")
//problemSetS.add("C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SET\\SET833-2.spass")
    var errorCountT = 0
    var totalCountT = 0
    var noresT = 0
    var otherT = 0
    var mrrresT = 0
    var cantfindT = 0
    var reqfailT = 0
    var parseT = 0
    var mrrassumptionT = 0

//    val elogger = new PrintWriter("errors.elog")
//    val eTypeLogger = new PrintWriter("errorTypes.elog")
//    val eProblemsLogger = new PrintWriter("errorProblems.elog")
    val etempT = new PrintWriter("etemp.elog")

    for (probY <- problemSetS) {
//      val probX = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\GRP\\GRP028-1.spass"
      println(totalCountT + " " + probY)
//      etempT.println(probY + " " + totalCountT + " OVERFLOW")
//      etempT.flush
      totalCountT = totalCountT + 1
      var proofLengthII = 0
      try {

        val proofToTest = ProofParserSPASS.read(probY)

//        println("length: " + proof.size)
//        println(proof)
        proofLengthII = proofToTest.size
      etempT.println(probY + " " + proofLengthII + " ")
      etempT.flush        
        println(FOLowerUnits(proofToTest))
        //        FORecyclePivotsWithIntersection(proof)
      } catch {
        case pe: ParserException => {
          parseT = parseT + 1
          errorCountT = errorCountT + 1
          etempT.println(probY)
          etempT.flush()
        }
        case exce: Exception => {
//          eProblemsLogger.println(probY)
          if (exce.getMessage() != null) {
            if (exce.getMessage().equals("Resolution: the conclusions of the given premises are not resolvable. A")) {
              noresT = noresT + 1
              //              etemp.println(p)
              //              etemp.flush()
            } else if (exce.getMessage().equals("Resolution (MRR): the conclusions of the given premises are not resolvable.")) {
              mrrresT = mrrresT + 1
              etempT.println(probY + " " + proofLengthII + " MRR")
              etempT.flush()
            } else if (exce.getMessage().equals("Resolution: Cannot find desired resolvent")) {
              etempT.println(probY + " " + proofLengthII + " can't find")
              etempT.flush()
              cantfindT = cantfindT + 1
              //                            etemp.println(p)
              //              etemp.flush() 
            } else if (exce.getMessage().equals("MRR assumption failed")) {
              mrrassumptionT = mrrassumptionT + 1
            } else if (exce.getMessage().equals("requirement failed")) {
              reqfailT = reqfailT + 1
            } else {
              etempT.println(probY + " " + proofLengthII+ " other" + exce.getMessage())
              etempT.flush()
              otherT = otherT + 1
            }
          } else {
            otherT = otherT + 1
            etempT.println(probY + " " + proofLengthII + " other")
            etempT.flush()
          }
          errorCountT = errorCountT + 1
          exce.printStackTrace()
//          exce.printStackTrace(elogger)
//          elogger.flush
        }
      }
    }
    println("total: " + totalCountT)
    println("errors: " + errorCountT)
    println("   nores: " + noresT)
    println("   other: " + otherT)
    println("  mrrres: " + mrrresT)
    println("cantfind: " + cantfindT)
    println(" reqfail: " + reqfailT)
    println("   parse: " + parseT)
    println("mrrassumption: " + mrrassumptionT)

//    elogger.flush
//    eTypeLogger.flush
//    eProblemsLogger.flush
  }
}



