package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
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

  
  def countNonResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for(n <- p.nodes){
    	if(!n.isInstanceOf[UnifyingResolution]){
    	  count = count + 1
    	}
    }
    count
  }

    def countResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for(n <- p.nodes){
    	if(n.isInstanceOf[UnifyingResolution]){
    	  count = count + 1
    	}
    }
    count
  }
  
  
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

    val path = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\"
    val proofList = "C:\\Users\\Jan\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\all_good_nov10.txt"

    val problemSetS = getProblems(proofList, path)
//    var errorCountT = 0
    var totalCountT = 0

    //    val elogger = new PrintWriter("errors.elog")
    //    val eTypeLogger = new PrintWriter("errorTypes.elog")
    //    val eProblemsLogger = new PrintWriter("errorProblems.elog")
    val etempT = new PrintWriter("results.log")

    for (probY <- problemSetS) {
      totalCountT = totalCountT + 1
      try {

        val proofToTest = ProofParserSPASS.read(probY)

        val proofLength = proofToTest.size
        val startTime = System.nanoTime
        val compressedProof = FOLowerUnits(proofToTest)
        val endTime = System.nanoTime
        val runTime = endTime-startTime
        val compressedLengthAll = compressedProof.size
        val compressedLengthResOnly = countResolutionNodes(compressedProof)
          etempT.println(probY + ",1," + proofLength + ","+compressedLengthAll+","+compressedLengthResOnly+","+runTime)
          etempT.flush        
      } catch {
        case e: CompressionException => {
          val proofToTest = ProofParserSPASS.read(probY)

          val proofLength = proofToTest.size

          etempT.println(probY + ",0," + proofLength + ",-1,-1,-1")
          etempT.flush
        }
      }

    }

    println("total: " + totalCountT)


    //    elogger.flush
    //    eTypeLogger.flush
    //    eProblemsLogger.flush
  }
}



