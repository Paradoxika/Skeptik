package at.logic.skeptik.experiments

import at.logic.skeptik.algorithm.compressor.FORecyclePivotsWithIntersection
import at.logic.skeptik.expression.Var
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.{ SequentProofNode => Node }
import java.io.PrintWriter
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
import collection.mutable.{Set => MSet}
import at.logic.skeptik.proof.Proof
import java.util.Calendar
import at.logic.skeptik.algorithm.FOProofsGenerator.ProofGenerator
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import scala.collection.mutable.{Set => MSet}
/**
 * Created by eze on 2016.07.25..
 * modified by jgorzny (November 2016)
 */
object FORPIProofGeneratorTestDebugger {
  var n = 0

  def main(arfs: Array[String]): Unit = {
    //testContraction()
    //randomLiteralTest()
    compressionTests(1000, 7, 1)
    //tests(1000,7,1)
    //f()
  }

  def getTimeString(): String = {
    val today = Calendar.getInstance().getTime()
    val out = today.toString().replace(":", "-")
    out
  }

  def f(): Unit = {
    var proof: Proof[Node] = null
    try {
      while (true) {
        proof = proofGenerationTest(2, Sequent()())._1
        FORecyclePivotsWithIntersection(proof)
      }
    } catch {
      case e: Exception =>
        println("\n" + proof)
        println("\n" + e)
    }
  }

  def countNonResolutionNodes(p: Proof[Node]): Int = {
    var count = 0
    for (n <- p.nodes) {
      if (!n.isInstanceOf[UnifyingResolution]) {
        count = count + 1
      }
    }
    count
  }

  def countFOSub(p: Proof[Node]): Int = {
    var count = 0
    for (n <- p.nodes) {
      if (n.isInstanceOf[FOSubstitution]) {
        count = count + 1
      }
    }
    count
  }
  def countResolutionNodes(p: Proof[Node]): Int = {
    var count = 0
    for (n <- p.nodes) {
      if (n.isInstanceOf[UnifyingResolution] || n.isInstanceOf[UnifyingResolutionMRR]) {
        count = count + 1
      }
    }
    count
  }

  def countResolutionNodesRandom(p: Proof[Node]): Int = p.size //This is okay when the proof is randomly generated
  //as such proofs do not contain resolution nodes anyway

  def compressionTests(proofN: Int, height: Int, timeout: Int): Unit = {
//    var proofsLenghtsSum = 0
//    var rpiProofsLenghtsSum = 0
    //    var splitProofsLenghtsSum = 0
//    var rpiN = 0
//    var rpiF = 0
    //    var splN      = 0
    //    var splF      = 0
    //    var splAv     = 0.0
//    var rpiAv = 0.0
    //    var splitFail = 0
//    var rpiFail = 0
    //    var c = 0

//    val outfile = "random-results-" + getTimeString() + ".txt"
//    val stats = new PrintWriter(outfile)

    for (h <- 1 to proofN) {

      print("Proof #: " + h)

      val (proof, vars) = proofGenerationTest(height, Sequent()())
//      proofsLenghtsSum += proof.size

      var rpiCompressedProof: Proof[Node] = null
//      var rpiLUproof: Proof[Node] = null
//      var luproof: Proof[Node] = null
//      var luRPIproof: Proof[Node] = null

      println(" Compression starting...")

//      var LUfail = false
      var RPIfail = false
//      var LURPIfail = false
//      var RPILUfail = false

//      var luFails = 0
      var rpiFails = 0
//      var rpiluFails = 0
//      var lurpiFails = 0

//      val luStartTime = System.nanoTime()
//
//      val luProof = try {
//        FOLowerUnits(proof)
//      } catch {
//        case e: Exception => {
//          LUfail = true
//          luFails = luFails + 1
//          proof
//        }
//        case a: AssertionError => {
//          LUfail = true
//          luFails = luFails + 1
//          proof
//        }
//      }
//      val luFinishTime = System.nanoTime()

      val rpiStartTime = System.nanoTime()
      try {
      FORecyclePivotsWithIntersection(proof)
      } catch {
        case e: Exception => {
          RPIfail = true
          rpiFails = rpiFails + 1
          e.printStackTrace()
          println(proof)
          assert(false)
        }
        case a: AssertionError => {
          RPIfail = true
          rpiFails = rpiFails + 1
          a.printStackTrace()
                    println(proof)
         assert(false)

        }
        }

//      val rpiProof = try {
//        FORecyclePivotsWithIntersection(proof)
//      } catch {
//        case e: Exception => {
//          RPIfail = true
//          rpiFails = rpiFails + 1
//          proof
//        }
//        case a: AssertionError => {
//          RPIfail = true
//          rpiFails = rpiFails + 1
//          proof
//        }
//      }
//      val rpiFinishTime = System.nanoTime()

//      val luRPIStartTime = System.nanoTime()
//      val luRPIProof = try {
//        FOLowerUnits(rpiProof)
//      } catch {
//        case e: Exception => {
//          LURPIfail = true
//          lurpiFails = lurpiFails + 1
//          if (!RPIfail) { luFails = luFails + 1 }
//          rpiProof
//        } 
//        case a: AssertionError => {
//          LURPIfail = true
//          lurpiFails = lurpiFails + 1
//          if (!RPIfail) { luFails = luFails + 1 }
//          rpiProof
//        }
//      }
//      val luRPIFinishTime = System.nanoTime()
//
//      val rpiLUStartTime = System.nanoTime()
//      val rpiLUProof = try {
//        FORecyclePivotsWithIntersection(luProof)
//      } catch {
//        case e: Exception => {
//          RPILUfail = true
//          rpiluFails = rpiluFails + 1
//          if (!LUfail) { rpiFails = rpiFails + 1 }
//          luProof
//        }
//        case a: AssertionError => {
//          RPILUfail = true
//          rpiluFails = rpiluFails + 1
//          if (!LUfail) { rpiFails = rpiFails + 1 }
//          luProof
//        }
//      }
//      val rpiLUFinishTime = System.nanoTime()

//      val rpiTime = (rpiFinishTime - rpiStartTime)
//      val luTime = (luFinishTime - luStartTime)
//      val lurpiTime = (luRPIFinishTime - luRPIStartTime)
//      val rpiluTime = (rpiLUFinishTime - rpiLUStartTime)
//      val totalTime = (rpiTime + luTime + lurpiTime + rpiluTime)
//
//      stats.print(h + ",")
//      printStats(stats, proof, rpiProof, RPIfail, rpiTime)
//      stats.print(",")
//      printStats(stats, proof, luProof, LUfail, luTime)
//      stats.print(",")
//      printStats(stats, proof, rpiLUProof, RPILUfail, luTime + rpiluTime)
//      stats.print(",")
//      printStats(stats, proof, luRPIProof, LURPIfail, rpiTime + lurpiTime)
//      stats.println("," + totalTime)

    }


  }

  def printStats(statWriter: PrintWriter, proof: Proof[Node], cProof: Proof[Node], fail: Boolean, time: Long) = {
    addStatsToLine(statWriter, fail, proof.size, countResolutionNodes(proof), cProof.size, countResolutionNodes(cProof),
      time, countFOSub(proof), countFOSub(cProof))
  }

  def addStatsToLine(statWriter: PrintWriter, fail: Boolean, size: Int, resSize: Int, cSize: Int,
                     cResSize: Int, time: Long, nFO: Int, nCFO: Int) {
    if (!fail) {
      val cRatio = ((cSize * 1.0) / (size * 1.0))
      val cResRatio = ((cResSize * 1.0) / (resSize * 1.0))
      statWriter.print(size + "," + resSize + "," + cSize + "," + cResSize + "," + cRatio + "," + cResRatio + "," + nFO + "," + nCFO + "," + time)
    } else {
      val failString = "-1"
      statWriter.print(size + "," + resSize + "," + failString + "," + failString + "," + failString + "," + failString + "," + nFO + "," + failString + "," + time)
    }
    statWriter.flush()
  }

  def randomLiteralTest() = {
    val generator = new ProofGenerator(10)
    println(generator.generateRandomLiteral())
  }

  def generateResolutionTest() = {
    val generator = new ProofGenerator(10)
    println(generator.generateResolution(Sequent()()))
    println("")
  }

  def proofGenerationTest(proofHeight: Int, root: Sequent): (Proof[Node], MSet[Var]) = {
    val generator = new ProofGenerator(proofHeight)
    try {
      (generator.generateProof(root), generator.getVariables())
    } catch {
      case e: Exception =>
        //println("FAIL\n" + e + "\n")
        proofGenerationTest(proofHeight, root)
    }
  }

}
