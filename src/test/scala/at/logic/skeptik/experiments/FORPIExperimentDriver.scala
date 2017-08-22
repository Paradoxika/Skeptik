package at.logic.skeptik.experiments

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.parser.ProofParserSPASS
import scala.io.Source
import at.logic.skeptik.algorithm.compressor.FOLowerUnits
import at.logic.skeptik.algorithm.compressor.FORecyclePivotsWithIntersection
import at.logic.skeptik.expression._
import collection.mutable.{HashSet => MSet}
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import java.io.PrintWriter
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
import java.util.Calendar 
import at.logic.skeptik.algorithm.compressor.CompressionException
import at.logic.skeptik.algorithm.compressor.checkProofEquality
import scala.collection.mutable.{HashSet => MSet}
import at.logic.skeptik.experiments.FORPIProofGeneratorTestsDir.printCompressedProof


/*
 * jgorzny
 * November 2016
 * This file used to collect data for algorithms on the CADE data set 
 * 
 * 
 */

object FORPIExperimentDriver extends checkProofEquality {

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
    if(p == null){
      return 0
    }
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

    def getTimeString(): String = {
    val today = Calendar.getInstance().getTime()
    val out = today.toString().replace(":","-")
    out
  }
  
  def main(args: Array[String]): Unit = {
    val logProofs = true
    val useBoth = true
    
    val prefixLen = "D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs".length() 
    val path = "D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\"
    val proofList = "D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\all_good_nov10.txt"

    val compressedProofDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Compressed\\15 Aug 2017 - CADE\\Proofs\\"
    
    
    val expPrefix = "CADE-FORPILU " + getTimeString()
    
    val problemSetS = getProblems(proofList, path)
    var errorCount = 0
    var parseErrorCount = 0
    var totalCount = 0
    var successCount = 0
    

    val parseErrorLogger = new PrintWriter(expPrefix + "_parseErrors.txt")
    
    val compressionErrorLogger = new PrintWriter(expPrefix + "_compressionErrors.txt")
    //    val eTypeLogger = new PrintWriter("errorTypes.elog")
    //    val eProblemsLogger = new PrintWriter("errorProblems.elog")
    val etempT = new PrintWriter(expPrefix + "_results.txt")
    val header = "proof,compressed?,length,resOnlyLength,compressedLengthAll,compressedLengthResOnly,compressTime,compressRatio,compressSpeed,compressRatioRes,compressSpeedRes,numFOSub,totalTime"
    etempT.println(header)
    etempT.flush
    val noDataString = ",-1,-1,-1,-1,-1,-1,-1,-1,-1"

    var totalNodes = 0
    var compressedNodes = 0
    
    for (probY <- problemSetS) {
      totalCount = totalCount + 1
      try {
        println("Parsing: " + probY)
        val preParseTime = System.nanoTime
        val proofToTest = try {
           ProofParserSPASS.read(probY)
        } catch {
          case e: Exception =>{
              println(probY + " COULD NOT BE PARSED")
              parseErrorLogger.println(probY)
              parseErrorCount = parseErrorCount + 1
              null
          }
        }
        val postParseTime = System.nanoTime
        
        val proofLength = if (proofToTest != null) { proofToTest.size } else { 0 }
        val numRes = countResolutionNodes(proofToTest)
        val parseTime = postParseTime-preParseTime
        
        val startTime = System.nanoTime
        totalNodes = proofLength + totalNodes
        
        val proofToTestB = try {
//          val q = FORecyclePivotsWithIntersection(proofToTest)
          val q = FOLowerUnits(proofToTest)
          
          
          if(q.root.conclusion.ant.size != 0 || q.root.conclusion.suc.size != 0){
            proofToTest
          } else {
            q
          }
        } catch {
          case t: Throwable => {
            proofToTest
          }
        }
        
        if(proofToTestB != null && logProofs) {
          val collectedProofPrefix = compressedProofDir + "CADE-results-" + startTime + "-proof-"
          val collectedProofSuffix = ".txt"
          printCompressedProof(proofToTestB, compressedProofDir, collectedProofSuffix, totalCount, "lu")
        }
        
         
        val compressedProof = if (proofToTestB != null && useBoth) {
//        val compressedProof =  if (proofToTest != null) { 
          try{
            //RPI used in try
            val p = FORecyclePivotsWithIntersection(proofToTest)
//            val p = FOLowerUnits(proofToTest)
            if(p.root.conclusion.ant.size != 0 || p.root.conclusion.suc.size != 0) { throw new Exception("not empty") }                         
            p
            //LU used in try
//            val p = FOLowerUnits(proofToTest)            
//            if(p.root.conclusion.ant.size != 0 || p.root.conclusion.suc.size != 0) { proofToTest } else { p }
          } catch {
            case f: Exception => {
              //RPI used in try
              compressionErrorLogger.println(probY)
              errorCount = errorCount + 1
              null 
              //LU used in try
//              proofToTest
            }
          }
          } else { 
            if (!useBoth && proofToTestB != null) { proofToTestB } else { null }
          }

        if(proofToTestB != null && logProofs) {
          val collectedProofPrefix = compressedProofDir + "CADE-results-" + startTime + "-proof-"
          val collectedProofSuffix = ".txt"
          printCompressedProof(proofToTestB, compressedProofDir, collectedProofSuffix, totalCount, "rpilu")
        }
        
        compressedNodes = if (compressedProof != null) { compressedNodes + compressedProof.size} else { compressedNodes} 
        
        if (compressedProof == null || compressedProof.root.conclusion.ant.size != 0 || compressedProof.root.conclusion.suc.size != 0) {
          etempT.println(probY.substring(prefixLen) + ",0," + proofLength + "," + numRes + noDataString + "-ERROR")
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
          
          if (compressionRatioRes < 0) { //Error
            etempT.println(probY.substring(prefixLen) + ",0," + proofLength + "," + numRes + noDataString)
            etempT.flush
          } else if (compressionRatioRes == 0){ //No compression
            etempT.println(probY.substring(prefixLen) + ",0," + proofLength + "," + numRes + "," + compressedLengthAll + ","
              + compressedLengthResOnly + "," + runTime + "," + compressionRatio + "," + compressionSpeed + "," + compressionRatioRes + "," + compressionSpeedRes+","+numSub+","+parseTime)
            etempT.flush
          } else { //Compression
            successCount = successCount + 1
            etempT.println(probY.substring(prefixLen) + ",1," + proofLength + "," + numRes + "," + compressedLengthAll + ","
              + compressedLengthResOnly + "," + runTime + "," + compressionRatio + "," + compressionSpeed + "," + compressionRatioRes + "," + compressionSpeedRes+","+numSub+","+parseTime)
            etempT.flush
          }
        }
      } catch {
        case e: CompressionException => {
          val proofToTest = ProofParserSPASS.read(probY)

          val proofLength = proofToTest.size
          val numRes = countResolutionNodes(proofToTest)

          etempT.println(probY.substring(prefixLen) + ",0," + proofLength + "," + numRes + noDataString)
          etempT.flush
        }
      }

    }

    println("Total: " + totalCount)
    println("Parse Errors: " + parseErrorCount)
    println("Compression Errors: " + errorCount)
    println("Succesful count: " + successCount)
    
    println("---")
    println("total: " + totalNodes)
    println("compr: " + compressedNodes)
    parseErrorLogger.flush
    parseErrorLogger.close
    
    compressionErrorLogger.flush
    compressionErrorLogger.close

  }
}



