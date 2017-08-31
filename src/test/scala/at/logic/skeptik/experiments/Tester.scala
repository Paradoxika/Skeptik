package at.logic.skeptik.experiments

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.parser.ProofParserSkeptikOutput
import at.logic.skeptik.parser.ProofParserSPASS
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.judgment.immutable.{ SetSequent => IClause }
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
import at.logic.skeptik.algorithm.compressor.FOCollectEdgesUsingSafeLiterals
import at.logic.skeptik.algorithm.compressor.FOAbstractRPIAlgorithm
import at.logic.skeptik.algorithm.compressor.FOLowerUnits
import at.logic.skeptik.algorithm.compressor.FORecyclePivotsWithIntersection

import at.logic.skeptik.algorithm.compressor.FOCollectEdgesUsingSafeLiterals
import at.logic.skeptik.algorithm.compressor.checkProofEquality
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}

object Tester extends FOAbstractRPIAlgorithm with FOCollectEdgesUsingSafeLiterals with checkProofEquality {
  def apply(proof: Proof[SequentProofNode]) = {
    proof
    //  FORecyclePivots(proof)
  }
  protected def computeSafeLiterals(proof: SequentProofNode,
                                    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
                                    edgesToDelete: FOEdgesToDelete): IClause = {
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof) } match {
      case Nil =>
        if (!childrensSafeLiterals.isEmpty) edgesToDelete.markBothEdges(proof)
        proof.conclusion.toSetSequent
      case h :: t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) =>
          {
            acc intersect safeLiteralsFromChild(v, proof, edgesToDelete)
          }
        }
    }
  }
  def main(args: Array[String]): Unit = {
 

    val pDir = "D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Proofs\\"

    //wednesday -3
//    val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 01-03-41 EST 2016-proof-50.txt")
//val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 11-34-37 EST 2016-proof-10.txt")
//val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 13-57-09 EST 2016-proof-107.txt")
//val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 13-57-09 EST 2016-proof-226.txt")
//val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 15-06-12 EST 2016-proof-48.txt")
//val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 15-06-12 EST 2016-proof-86.txt")
//val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 15-27-23 EST 2016-proof-254.txt")
//    val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Mon Nov 21 23-12-55 EST 2016-proof-108.txt")//-4 ; not an issue for RPI
    //val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 15-06-12 EST 2016-proof-41.txt") //rpi blue dot

    
    
//  val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 15-27-23 EST 2016-proof-279.txt")//initial - unif
//  val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Mon Nov 21 23-12-55 EST 2016-proof-68.txt") //now fixed - unif
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN632-1.spass") //bad comp
    
    
    //Jan 6
//    val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Mon Nov 21 23-12-55 EST 2016-proof-112.txt") //change fR to FL ****
//    val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 11-36-10 EST 2016-proof-20.txt") //change fR to FL ****
//    val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Mon Nov 21 23-12-55 EST 2016-proof-273.txt") //change fR to fL ****
//    val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 14-31-43 EST 2016-proof-201.txt") // check both including auxR too
    
//    val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 13-57-09 EST 2016-proof-149.txt")
//    val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 14-31-43 EST 2016-proof-150.txt")
    
    //these are fixed
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN569-1.spass")     
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN562-1.spass")
//    
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN632-1.spass")
    
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\MGT\\MGT004-1.spass")     
    
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 16-54-07 EST 2016-proof-70.txt")
  
//  val proof = ProofParserSkeptikOutput.read(pDir + "random-results-Tue Nov 22 15-27-23 EST 2016-proof-295.txt")
  
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 11-49-03 EST 2016-proof-105.txt")
    
//        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 23-12-55 EST 2016-proof-283.txt") //does not finish quickly (prior to aug 16)
      //Aug 2017  
//val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 23-12-55 EST 2016-proof-171.txt")         
//val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 23-12-55 EST 2016-proof-310.txt")         
//val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 12-19-23 EST 2016-proof-24.txt")         
//val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 13-57-09 EST 2016-proof-149.txt") //mrr         
//val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 14-31-43 EST 2016-proof-5.txt")         
    
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 15-06-12 EST 2016-proof-115.txt")

    
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\MGT\\MGT007-1.spass")
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN687-1.spass")
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\GRP\\GRP031-2.spass") 
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN636-1.spass")
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN562-1.spass")//fixed
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN622-1.spass")
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN570-1.spass")
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN325-1.spass")
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\COM\\COM002-2.spass") 
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN632-1.spass")//fixed 
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\MGT\\MGT004-1.spass") 
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN717-1.spass")//
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\SYN\\SYN569-1.spass")// 
    
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 23-12-55 EST 2016-proof-231.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 14-31-43 EST 2016-proof-162.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 14-31-43 EST 2016-proof-201.txt")//
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 15-27-23 EST 2016-proof-76.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 16-40-48 EST 2016-proof-6.txt") //QF in FA
    
//val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 15-27-23 EST 2016-proof-214.txt") //hung?
    
    
    //LU
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 22-28-48 EST 2016-proof-1.txt")
    
    
    //combined CADE
//    val proof = ProofParserSPASS.read("D:\\Documents\\Google Summer of Code 2014\\Experiments\\NoMRR\\GoodProofs\\GRP\\GRP028-4.spass")//
    
    //-3
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 16-54-07 EST 2016-proof-85.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 22-58-03 EST 2016-proof-29.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 01-03-41 EST 2016-proof-37.txt")
//        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 01-03-41 EST 2016-proof-35.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 11-49-03 EST 2016-proof-100.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 16-54-07 EST 2016-proof-52.txt") //FR/FL
    
    //-1
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 23-12-55 EST 2016-proof-112.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 23-12-55 EST 2016-proof-124.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 11-36-10 EST 2016-proof-20.txt")
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 15-06-12 EST 2016-proof-23.txt")
    //-3-LU fail i.e. treat as -1
//        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 23-12-55 EST 2016-proof-112.txt")
//        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Mon Nov 21 23-12-55 EST 2016-proof-124.txt")
//            val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 11-36-10 EST 2016-proof-20.txt")
//           val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 13-57-09 EST 2016-proof-128.txt")
//        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 15-06-12 EST 2016-proof-23.txt")

    //-3 - legit
//    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 01-03-41 EST 2016-proof-44.txt")
//        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 13-57-09 EST 2016-proof-138.txt")
//        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 13-57-09 EST 2016-proof-49.txt")//
        

    //-1
//      val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 12-19-23 EST 2016-proof-107.txt")//
//      val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 12-19-23 EST 2016-proof-56.txt")//
//      val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 14-31-43 EST 2016-proof-150.txt")//
    //-3
//      val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 12-19-23 EST 2016-proof-107.txt")//lu fails
//      val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 12-19-23 EST 2016-proof-56.txt")//lu fails
//      val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 14-31-43 EST 2016-proof-150.txt")//lu fails
//      val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 15-27-23 EST 2016-proof-174.txt")//
      
        //-3
//        val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 15-27-23 EST 2016-proof-174.txt")//
        
        //Really good compression example
    val proof = ProofParserSkeptikOutput.read("D:\\Research Data\\GSoC14\\November 2016 Random Proof Data\\Generated\\21 Nov 2016\\Retest\\random-results-Tue Nov 22 16-54-07 EST 2016-proof-112.txt")
        
        
    println(proof)
//     println(proof.size)
     
    println("-------------------------------------------------------------------")
    val iProof = try {
//     val dProof = FORecyclePivotsWithIntersection(proof)
//          val dProof = FOLowerUnits(proof)
          val dProof = FORecyclePivotsWithIntersection(FOLowerUnits(proof)) // this is the real test
//                val dProof = FOLowerUnits(FORecyclePivotsWithIntersection(proof))

     if(dProof.root.conclusion.ant.size != 0 || dProof.root.conclusion.suc.size != 0){
       println(dProof)
       println("Bad compression.")
       proof
     } else {
       println(dProof)
       dProof
     }
     } catch {
       case e: Exception => {
         e.printStackTrace()
         proof
       }
     }
       def countResolutionNodes(p: Proof[SequentProofNode]): Int = {
    var count = 0
    for (n <- p.nodes) {
      if (n.isInstanceOf[UnifyingResolution] || n.isInstanceOf[UnifyingResolutionMRR]) {
        count = count + 1
      }
    }
    count
  }
     println(countResolutionNodes(proof) + " "  + countResolutionNodes(iProof))
     println(proof.size + " " + iProof.size)
     
     //print(iProof)
//    println("-------------------------------------------------------------------")
//    try{
//     val cProof =  FORecyclePivotsWithIntersection(iProof) //try with iProof
//     println(proof.size, cProof.size)
//     println(cProof)
//    }catch {
//      case f: Throwable =>{
//        f.printStackTrace()
////println(proof.size, iProof.size)        
//      }
//    }
     

 
    
     
//           var LUfail = false
//      var RPIfail = false
//      var LURPIfail = false
//      var RPILUfail = false
//
//      var RPIfailAfterLU = false
//      var LUfailAfterRPI = false
//      
//      var luFails = 0
//      var rpiFails = 0
//      var rpiluFails = 0
//      var lurpiFails = 0
//
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
//
//      println("LU Done.")
//      println(luProof)
//      
//      val rpiStartTime = System.nanoTime()
//
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
//      println("RPI Done.")
//      println(rpiProof)
//
//      
//      val luRPIStartTime = System.nanoTime()
//      val luRPIProof = try {
//        FOLowerUnits(rpiProof)
//      } catch {
//        case e: Exception => {
//          if (RPIfail) { LURPIfail = true 
//          } else { LUfailAfterRPI = true }
//          rpiProof
//        } 
//        case a: AssertionError => {
//          if (RPIfail) { LURPIfail = true 
//          } else { LUfailAfterRPI = true }
//          rpiProof
//        }
//      }
//      val luRPIFinishTime = System.nanoTime()
//      println("LURPI Done.")
//      val rpiLUStartTime = System.nanoTime()
//      val rpiLUProof = try {
//        FORecyclePivotsWithIntersection(luProof)
//      } catch {
//        case e: Exception => {
//          if (LUfail) { RPILUfail = true 
//          } else { RPIfailAfterLU = true }
//          luProof
//        }
//        case a: AssertionError => {
//          if (LUfail) { RPILUfail = true  
//          } else { RPIfailAfterLU = true }
//          luProof
//        }
//      }
//      val rpiLUFinishTime = System.nanoTime()
//      println("RPILU Done.")
//      println(rpiLUProof)
//     
//      
//      val rpiTime = (rpiFinishTime - rpiStartTime)
//      val luTime = (luFinishTime - luStartTime)
//      val lurpiTime = (luRPIFinishTime - luRPIStartTime)
//      val rpiluTime = (rpiLUFinishTime - rpiLUStartTime)
//      val totalTime = (rpiTime + luTime + lurpiTime + rpiluTime)
//  
//      printStats( proof, rpiProof, RPIfail, rpiTime, "-1")
//      print(",")        
//      printStats( proof, luProof, LUfail, luTime, "-2")
//      print(",")
//      printStats( proof, rpiLUProof, RPILUfail, luTime + rpiluTime, "-3")
//      print(",")
//      printStats(proof, luRPIProof, LURPIfail, rpiTime + lurpiTime, "-4")
  

  
  }
  def printStats(sproof: Proof[SequentProofNode], cProof: Proof[SequentProofNode], fail: Boolean, time: Long, failString: String) = {
    addStatsToLine(fail, sproof.size, countResolutionNodes(sproof), cProof.size, countResolutionNodes(cProof),
      time, countFOSub(sproof), countFOSub(cProof), failString)
  }

  def addStatsToLine(fail: Boolean, size: Int, resSize: Int, cSize: Int,
                     cResSize: Int, time: Long, nFO: Int, nCFO: Int, failString: String) {
    if (!fail) {
      val cRatio = ((cSize * 1.0) / (size * 1.0))
      val cResRatio = ((cResSize * 1.0) / (resSize * 1.0))
      print(size + "," + resSize + "," + cSize + "," + cResSize + "," + cRatio + "," + cResRatio + "," + nFO + "," + nCFO + "," + time)
    } else {
      print(size + "," + resSize + "," + failString + "," + failString + "," + failString + "," + failString + "," + nFO + "," + failString + "," + time)
    }
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
      if (n.isInstanceOf[UnifyingResolution] || n.isInstanceOf[UnifyingResolutionMRR]) {
        count = count + 1
      }
    }
    count
  }
  
}



