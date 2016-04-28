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
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution

object CADEExperimentDriver extends checkProofEquality {

  def countNonResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes) {
      if (!n.isInstanceOf[UnifyingResolution]) {
        count = count + 1
      }
    }
    count
  }
  
  def countFOSub(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes) {
      if (n.isInstanceOf[FOSubstitution]) {
        count = count + 1
      }
    }
    count
  }

  def countResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes) {
      if (n.isInstanceOf[UnifyingResolution]) {
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
    val etempT = new PrintWriter("results-feb23.log")
    val header = "proof,compressed?,length,resOnlyLength,compressedLengthAll,compressedLengthResOnly,compressTime,compressRatio,compressSpeed,compressRatioRes,compressSpeedRes,numFOSub,totalTime"
    etempT.println(header)
    etempT.flush
    val noDataString = ",-1,-1,-1,-1,-1,-1,-1,-1,-1"

    for (probY <- problemSetS) {
      totalCountT = totalCountT + 1
      try {

        val preParseTime = System.nanoTime
        
        val proofToTest = ProofParserSPASS.read(probY)

        val postParseTime = System.nanoTime
        
        val proofLength = proofToTest.size
        val numRes = countResolutionNodes(proofToTest)
        val parseTime = postParseTime-preParseTime
        
        val startTime = System.nanoTime
        
        val compressedProof = FOLowerUnits(proofToTest)

        if (compressedProof.root.conclusion.ant.size != 0 || compressedProof.root.conclusion.suc.size != 0) {
          etempT.println(probY.substring(79) + ",0," + proofLength + "," + numRes + noDataString + "-ERROR")
          etempT.flush
        } else {

          val endTime = System.nanoTime
          val runTime = endTime - startTime
          val compressedLengthAll = compressedProof.size
          val compressedLengthResOnly = countResolutionNodes(compressedProof)

          val compressionRatio = (proofLength - compressedLengthAll) / proofLength.toDouble
          val compressionSpeed = (proofLength - compressedLengthAll) / runTime.toDouble

          val compressionRatioRes = (numRes - compressedLengthResOnly) / proofLength.toDouble
          val compressionSpeedRes = (numRes - compressedLengthResOnly) / runTime.toDouble

          val numSub = countFOSub(compressedProof)
          
          if (compressionRatioRes < 0) {
            etempT.println(probY.substring(79) + ",0," + proofLength + "," + numRes + noDataString)
            etempT.flush
          } else {

            etempT.println(probY.substring(79) + ",1," + proofLength + "," + numRes + "," + compressedLengthAll + ","
              + compressedLengthResOnly + "," + runTime + "," + compressionRatio + "," + compressionSpeed + "," + compressionRatioRes + "," + compressionSpeedRes+","+numSub+","+parseTime)
            etempT.flush
          }
        }
      } catch {
        case e: CompressionException => {
          val proofToTest = ProofParserSPASS.read(probY)

          val proofLength = proofToTest.size
          val numRes = countResolutionNodes(proofToTest)

          etempT.println(probY.substring(79) + ",0," + proofLength + "," + numRes + noDataString)
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



