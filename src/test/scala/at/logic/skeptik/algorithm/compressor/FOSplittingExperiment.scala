package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.resolution.{FOSubstitution, UnifyingResolution}
import at.logic.skeptik.parser.ProofParserSPASS

import collection.mutable.{HashSet => MSet}
import java.io.PrintWriter

import at.logic.skeptik.algorithm.compressor.FOSplit.FOCottonSplit

import scala.io.Source


/**
  * This object is created to
  */
object FOSplittingExperiment {

  def countNonResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes)
      if (!n.isInstanceOf[UnifyingResolution])
        count = count + 1
    count
  }

  def countFOSub(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes)
      if (n.isInstanceOf[FOSubstitution])
        count = count + 1
    count
  }

  def countResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes)
      if (n.isInstanceOf[UnifyingResolution])
        count = count + 1
    count
  }

  def getProblems(file: String, path: String): MSet[String] = {
    val outTj = MSet[String]()

    for (line <- Source.fromFile(file).getLines()) {
      val newProblemN = path + line
      println(newProblemN)
      outTj.add(newProblemN)
    }
    outTj
  }

  def main(args: Array[String]): Unit = {

    val path = "/home/eze/Escritorio/Skeptik/GoodProofs/ALL/"
    val proofList = "/home/eze/Escritorio/Skeptik/GoodProofs/ALL/list.txt"

    val problemSetS = getProblems(proofList, path)
    //    var errorCountT = 0
    var totalCountT = 0

    //    val elogger = new PrintWriter("errors.elog")
    //    val eTypeLogger = new PrintWriter("errorTypes.elog")
    //    val eProblemsLogger = new PrintWriter("errorProblems.elog")
    val etempT = new PrintWriter("results-FOSplitting.log")
    val header = "proof,compressed?,length,resOnlyLength,compressedLengthAll,compressedLengthResOnly,compressTime,compressRatio,compressSpeed,compressRatioRes,compressSpeedRes,numFOSub,totalTime"
    etempT.println(header)
    etempT.flush()
    val noDataString = ",-1,-1,-1,-1,-1,-1,-1,-1,-1"

    for (probY <- problemSetS) {
      totalCountT = totalCountT + 1
      try {

        val preParseTime = System.nanoTime

        println("Proof: " + probY)
        val proofToTest = ProofParserSPASS.read(probY)
        var variables   = ProofParserSPASS.getVars()
        //ProofParserSPASS.cleanVars()
        println("Variables: " + variables.mkString(","))
        println(proofToTest)

        val postParseTime = System.nanoTime

        val proofLength = proofToTest.size
        val numRes = countResolutionNodes(proofToTest)
        val parseTime = postParseTime-preParseTime

        val startTime = System.nanoTime

        val timeout = 4000
        val cottonSplit = new FOCottonSplit(variables,timeout)
        val compressedProof = cottonSplit(proofToTest)
        val resNodesAfter = countResolutionNodes(compressedProof)
        if(resNodesAfter < numRes) {
          println("Proof after split has "+ (numRes - resNodesAfter) + "less nodes resolution nodes")
          println(compressedProof)
        } else {
          println("The proof was not compressed\n\n")
          println(compressedProof)
          println("\n\n#########################################\n\n")
        }

        if (compressedProof.root.conclusion.ant.nonEmpty || compressedProof.root.conclusion.suc.nonEmpty) {
          etempT.println(probY.substring(path.length) + ",0," + proofLength + "," + numRes + noDataString + "-ERROR")
          etempT.flush()
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
            etempT.println(probY.substring(path.length) + ",0," + proofLength + "," + numRes + noDataString)
            etempT.flush()
          } else {

            etempT.println(probY.substring(path.length) + ",1," + proofLength + "," + numRes + "," + compressedLengthAll + ","
              + compressedLengthResOnly + "," + runTime + "," + compressionRatio + "," + compressionSpeed + "," + compressionRatioRes + "," + compressionSpeedRes+","+numSub+","+parseTime)
            etempT.flush()
          }
        }
      } catch {
        case e: CompressionException => {
          val proofToTest = ProofParserSPASS.read(probY)

          val proofLength = proofToTest.size
          val numRes = countResolutionNodes(proofToTest)

          etempT.println(probY.substring(path.length) + ",0," + proofLength + "," + numRes + noDataString)
          etempT.flush()
        }
      }

    }

    println("total: " + totalCountT)

    //    elogger.flush
    //    eTypeLogger.flush
    //    eProblemsLogger.flush
  }

}
