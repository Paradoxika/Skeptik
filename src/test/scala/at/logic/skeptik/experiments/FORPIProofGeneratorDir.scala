package at.logic.skeptik.experiments
import at.logic.skeptik.parser.ProofParserSkeptikOutput
import at.logic.skeptik.algorithm.compressor.{ FOLowerUnits, FORecyclePivotsWithIntersection }
import at.logic.skeptik.expression.Var
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.{ SequentProofNode => Node }
import java.io.PrintWriter
import java.io.File
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
import java.io.FileWriter

/**
 * Created by eze on 2016.07.25..
 * modified by jgorzny (November 2016)
 */
object FORPIProofGeneratorTestsDir {
  var n = 0

  def main(arfs: Array[String]): Unit = {
    //testContraction()
    //randomLiteralTest()
    compressionTests()
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

//  def countResolutionNodesRandom(p: Proof[Node]): Int = p.size //This is okay when the proof is randomly generated
//  //as such proofs do not contain resolution nodes anyway

  def printProof(w: PrintWriter, p: Proof[Node]){
    w.println(p)
  }
  
 def getListOfFiles(dir: String):List[File] = {
  val d = new File(dir)
  if (d.exists && d.isDirectory) {
    d.listFiles.filter(_.isFile).toList
  } else {
    List[File]()
  }
}  
  
  def compressionTests(): Unit = {
    var proofsLenghtsSum = 0
    var rpiProofsLenghtsSum = 0
    //    var splitProofsLenghtsSum = 0
    var rpiN = 0
    var rpiF = 0
    //    var splN      = 0
    //    var splF      = 0
    //    var splAv     = 0.0
    var rpiAv = 0.0
    //    var splitFail = 0
    var rpiFail = 0
    //    var c = 0

//    val proofDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Proofs\\"
    val compressedProofDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Compressed\\15 Aug 2017\\Proofs\\"
    val startTime = getTimeString()
    val outfile = "random-retest-results-" + startTime + ".txt"
    val stats = new PrintWriter(outfile)

    val pDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest"
    val files = getListOfFiles(pDir)
    
    var h = 0
    var totalParseTime = 0.asInstanceOf[Long]
    
    
    for (file <- files) {
      val pFileName = file.getAbsolutePath
      print("Proof #: " + h + " " + pFileName)
      
          val fw = new FileWriter("checking-subs.txt", true)
try {
  fw.write("Proof #: " + h + " " + pFileName + "\n")

}
finally fw.close() 
  

      val parseStartTime = System.nanoTime()      
      
      val proof = ProofParserSkeptikOutput.read(pFileName)//do things
      
      val parseEndTime = System.nanoTime()
      
      totalParseTime = totalParseTime + (parseEndTime - parseStartTime)
      
//      val proofFile = proofDir + "random-results-" + startTime + "-proof-" + h + ".txt"
//      val proofWriter = new PrintWriter(proofFile)
//      printProof(proofWriter, proof)
//      proofWriter.flush()
//      proofWriter.close()
      
      proofsLenghtsSum += proof.size

//      var rpiCompressedProof: Proof[Node] = null
//      var rpiLUproof: Proof[Node] = null
//      var luproof: Proof[Node] = null
//      var luRPIproof: Proof[Node] = null

      
      def printCompressedProof(proof: Proof[Node], pre: String, suf: String, h: Int, alg: String) = {
        val proofFile = pre + h.toString() + "-" + alg + "-" + suf
        val proofWriter =new PrintWriter(proofFile)
        printProof(proofWriter, proof)
        proofWriter.flush()
        proofWriter.close()
  
      }
      
      val collectedProofPrefix = compressedProofDir + "random-results-" + startTime + "-proof-"
      val collectedProofSuffix = ".txt"
      
      println(" Compression starting...")

      val oSize = proof.toSeq.size
      
      var LUfail = false
      var RPIfail = false
      var LURPIfail = false
      var RPILUfail = false

      var RPIfailAfterLU = false
      var LUfailAfterRPI = false
      
      var luFails = 0
      var rpiFails = 0
      var rpiluFails = 0
      var lurpiFails = 0

      val luStartTime = System.nanoTime()

      val luProof = try {
        val p = FOLowerUnits(proof)
        if(p.root.conclusion.ant.size != 0 || p.root.conclusion.suc.size != 0){
          LUfail = true
          luFails = luFails +1
          proof
        } else {
          printCompressedProof(p,collectedProofPrefix,collectedProofSuffix,h,"lu")
          p
        }
      } catch {
        case e: Exception => {
          LUfail = true
          luFails = luFails + 1
          proof
        }
        case a: AssertionError => {
          LUfail = true
          luFails = luFails + 1
          proof
        }
      }
      val luFinishTime = System.nanoTime()

      val afterLUsize = proof.toSeq.size
      assert(afterLUsize == oSize)
      
      val rpiStartTime = System.nanoTime()

      val rpiProof = try {
        val p = FORecyclePivotsWithIntersection(proof, pFileName)
        if(p.root.conclusion.ant.size != 0 || p.root.conclusion.suc.size != 0){
          RPIfail = true
          rpiFails = rpiFails +1
          proof
        } else {
          printCompressedProof(p,collectedProofPrefix,collectedProofSuffix,h,"rpi")
          p
        }
      
      } catch {
        case e: Exception => {
          RPIfail = true
          rpiFails = rpiFails + 1
          proof
        }
        case a: AssertionError => {
          RPIfail = true
          rpiFails = rpiFails + 1
          proof
        }
      }
      val rpiFinishTime = System.nanoTime()

      val afterRPIsize = proof.toSeq.size
      assert(afterRPIsize == oSize)      
      
      val luRPIStartTime = System.nanoTime()
      val luRPIProof = try {
        val p = FOLowerUnits(rpiProof)
        if(p.root.conclusion.ant.size != 0 || p.root.conclusion.suc.size != 0){
          LURPIfail = true //definitely want to report fail here
          rpiProof
        } else {
          printCompressedProof(p,collectedProofPrefix,collectedProofSuffix,h,"lurpi")          
          p
        }        
      } catch {
        case e: Exception => {
          if (RPIfail) { LURPIfail = true 
          } else { LUfailAfterRPI = true }
          rpiProof
        } 
        case a: AssertionError => {
          if (RPIfail) { LURPIfail = true 
          } else { LUfailAfterRPI = true }
          rpiProof
        }
      }
      val luRPIFinishTime = System.nanoTime()

      val rpiLUStartTime = System.nanoTime()
      val rpiLUProof = try {
        val p = FORecyclePivotsWithIntersection(luProof)
        if(p.root.conclusion.ant.size != 0 || p.root.conclusion.suc.size != 0){
          RPILUfail = true //definitely want to report fail here
          luProof
        } else {
          printCompressedProof(p,collectedProofPrefix,collectedProofSuffix,h,"rpilu")          
          p
        }                
      } catch {
        case e: Exception => {
          if (LUfail) { RPILUfail = true 
          } else { RPIfailAfterLU = true }
          luProof
        }
        case a: AssertionError => {
          if (LUfail) { RPILUfail = true  
          } else { RPIfailAfterLU = true }
          luProof
        }
      }
      val rpiLUFinishTime = System.nanoTime()

      val rpiTime = (rpiFinishTime - rpiStartTime)
      val luTime = (luFinishTime - luStartTime)
      val lurpiTime = (luRPIFinishTime - luRPIStartTime)
      val rpiluTime = (rpiLUFinishTime - rpiLUStartTime)
      val totalTime = (rpiTime + luTime + lurpiTime + rpiluTime)

      
      val rpiFailString = "-1"
      val luFailString = "-2"
      val rpiluFailString = "-3"
      val lurpiFailString = "-4"
      
      stats.print(h + ",")
      printStats(stats, proof, rpiProof, RPIfail, rpiTime, rpiFailString)
      stats.print(",")
      printStats(stats, proof, luProof, LUfail, luTime, luFailString)
      stats.print(",")
      printStats(stats, proof, rpiLUProof, RPILUfail, luTime + rpiluTime, rpiluFailString)
      stats.print(",")
      val LURPIfailb = RPIfail && LURPIfail
      printStats(stats, proof, luRPIProof, LURPIfailb, rpiTime + lurpiTime, lurpiFailString)
      stats.println("," + totalTime + "," + RPIfailAfterLU + "," + LUfailAfterRPI + "," + pFileName)

      /*
      if (countResolutionNodes(proof) > countResolutionNodes(rpiCompressedProof)
        && countResolutionNodes(rpiCompressedProof) > countResolutionNodes(proof) / 2) {
        rpiN += 1
        if (rpiCompressedProof.root.conclusion.ant.nonEmpty || rpiCompressedProof.root.conclusion.suc.nonEmpty) {
          rpiFail += 1
          stats.println(h + "," + proof.size + "," + countResolutionNodes(proof) + "," + "-1" + ","
            + "-1" + "," + "-1" + ","
            + "-1" + "," + "-1" + "," + timeElapsed)
          stats.flush()
        }
        rpiProofsLenghtsSum += rpiCompressedProof.size
        rpiAv += (countResolutionNodes(rpiCompressedProof) * 1.0) / countResolutionNodes(proof)
        println("FORPI: " + countResolutionNodes(proof) + " -> " + countResolutionNodes(rpiCompressedProof))
        stats.println(h + "," + proof.size + "," + countResolutionNodes(proof) + "," + rpiCompressedProof.size + ","
          + countResolutionNodes(rpiCompressedProof) + "," + countFOSub(rpiCompressedProof) + ","
          + ((proof.size * 1.0) / (rpiCompressedProof.size * 1.0)) + "," + ((countResolutionNodes(proof) * 1.0) / (countResolutionNodes(rpiCompressedProof) * 1.0)) + "," + timeElapsed)
        stats.flush()
      } else {
        rpiProofsLenghtsSum += proof.size
        stats.println(h + "," + proof.size + "," + countResolutionNodes(proof) + "," + "-1" + ","
          + "-1" + "," + "-1" + ","
          + "-1" + "," + "-1" + "," + timeElapsed)
        stats.flush()
      }
    }
    */
      h = h + 1
    }

//    println("Average proof size: " + (proofsLenghtsSum * 1.0) / proofN)
//    println("FORPI\nReduced: " + rpiN + " proof(s)\nFailed in: " + rpiF + " proof(s)\nThe average compression was to " + rpiAv / rpiN)
//    println("Total compression ratio: " + ((proofsLenghtsSum - rpiProofsLenghtsSum) * 1.0) / proofsLenghtsSum)
//    println("Number of fails RPI: " + rpiFail)
    println("parse time: " + totalParseTime)
    println("started: " + startTime)
    println("ended: " + getTimeString())
    
  }

  def printStats(statWriter: PrintWriter, proof: Proof[Node], cProof: Proof[Node], fail: Boolean, time: Long, failString: String) = {
    addStatsToLine(statWriter, fail, proof.size, countResolutionNodes(proof), cProof.size, countResolutionNodes(cProof),
      time, countFOSub(proof), countFOSub(cProof), failString)
  }

  def addStatsToLine(statWriter: PrintWriter, fail: Boolean, size: Int, resSize: Int, cSize: Int,
                     cResSize: Int, time: Long, nFO: Int, nCFO: Int, failString: String) {
    if (!fail) {
      val cRatio = ((cSize * 1.0) / (size * 1.0))
      val cResRatio = ((cResSize * 1.0) / (resSize * 1.0))
      statWriter.print(size + "," + resSize + "," + cSize + "," + cResSize + "," + cRatio + "," + cResRatio + "," + nFO + "," + nCFO + "," + time)
    } else {
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
