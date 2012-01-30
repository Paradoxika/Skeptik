/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package ResK.evaluation

import scala.collection.mutable._
import ResK.utilities.Utilities._
import ResK.calculi.resolution._
import ResK.calculi.resolution.measures._
import ResK.algorithms.Regularization._
import ResK.algorithms.DAGification._
import ResK.algorithms.ProofFixing._
import java.io.FileWriter

object Experimenter {

  implicit val maxUnnamedResolvents = 200


  def run(algorithms: List[(String, Proof => Proof)], measure: Proof => Int, directory: String, proofFiles: List[String], outputFilename: String) = {
    val writer = new FileWriter(directory + outputFilename)
    val runtime = Runtime.getRuntime()
    for (proofFile <- proofFiles) {
      println(proofFile)
      try {
        println("parsing")
        val p0 = removeUnusedResolvents(ResK.algorithms.ProofParser.getProofFromFile(directory + proofFile + ".proof"))

        println("outputting proof with a single root")
        ResK.algorithms.ProofExporter.writeProofToFile(p0, directory + proofFile + "(SingleRoot).proof")

        val inputMeasure = measure(p0)
        val outputMeasures = for (a <- algorithms) yield {
          println("forcing garbage collection")
          runtime.gc
          println("duplicating")
          val p = p0.duplicate
          println("running " + a._1)
          val startTime = System.nanoTime
          val newP = a._2(p)
          val time = (System.nanoTime - startTime)/1000000
          println("exporting to file")
          ResK.algorithms.ProofExporter.writeProofToFile(newP, directory + proofFile + "(" + a._1 + ").proof")
          println("measuring output")
          val m = (measure(newP),time)
          println((inputMeasure*1.0 - m._1)/inputMeasure)
          println(time)
          m
        }

        val compressionRatesAndTimes = ("" /: outputMeasures.map(m => "\t" + (inputMeasure*1.0 - m._1)/inputMeasure + "\t" + m._2 + "\t" + 1000.0*(inputMeasure*1.0 - m._1)/m._2))((s1, s2) => s1 + s2)


        val thisLine = inputMeasure +
                      compressionRatesAndTimes +
                      "\n"
        println(thisLine)
        writer.write(thisLine, 0, thisLine.length)
      } catch {
        case e => {throw e; println(proofFile); e.printStackTrace}
      }
    }
    writer.close
  }
  
  
  // Possibly not used code below this line. 
 
  
//    def run(directory: String, proofFiles: List[String], outputFilename: String) = {
//    val writer = new FileWriter(directory + outputFilename)
//    val firstLine = "Filename \t\t\t" +
//                    "InputLength \t" +
//                    //"InputSize \t" +
//                    //"InputAverageNumberOfChildrenPerNode \t" +
//                    "ParsingTime \t\t" +
//                    "R_Length \t" +            // length after regularization
//                    "R_Time \t" +              // regularization time
//                    "DAG_Length \t" +          // length after DAGification
//                    "DAG_Time \t" +            // DAGification time
//                    "RP_Length \t" +           // length after pivot recycling
//                    "RP_Time \t" +             // pivot recycling time
//                    "R-DAG_Length \t" +        // length after regularization and DAGification
//                    "R-DAG_Time \t" +            // regularization and DAGification time
//                    "\n"
//    //writer.write(firstLine, 0, firstLine.length)
//    for (proofFile <- proofFiles) {
//      println(proofFile)
//      println("parsing")
//      val startParsingTime = System.nanoTime
//      val p0 = proofCompression.ProofParser.getProofFromFile(directory + proofFile + ".proof")
//      val ellapsedParsingTime = (System.nanoTime - startParsingTime)/1000
//      val p1 = p0.duplicate
//      val p2 = p0.duplicate
//      val p3 = p0.duplicate
//      val inputLength = length(p1)
//
//      println("regularizing")
//      val startRTime = System.nanoTime
//      regularize(p1)
//      fix(p1)
//      val ellapsedRTime = (System.nanoTime - startRTime)/1000
//      val RLength = p1.length
//
//      println("removing new sinks")
//      val p4 = removeUnusedResolvents(p1)
//
//
//      println("DAGifying")
//      val startRDAGTime = System.nanoTime
//      DAGify(p4, p => p.length)
//      val ellapsedRDAGTime = (System.nanoTime - startRDAGTime)/1000 + ellapsedRTime
//      val RDAGLength = p4.length
//      //println("DAGified")
//
//      println("DAGifying the original proof")
//      val startDAGTime = System.nanoTime
//      DAGify(p2, p => p.length)
//      //println(isRegular(p2))
//      val ellapsedDAGTime = (System.nanoTime - startDAGTime)/1000
//      val DAGLength = p2.length
//
//      println("recycle pivots")
//      val startRPTime = System.nanoTime
//      recyclePivots(p3)
//      fix(p3)
//      val ellapsedRPTime = (System.nanoTime - startRPTime)/1000
//      val RPLength = p3.length
//      
//
//      val thisLine = inputLength + "\t" +
//                     //ellapsedParsingTime + "\t" +
//                     RLength*1.0/inputLength + "\t" +
//                     //ellapsedRTime + "\t" +
//                     DAGLength*1.0/inputLength + "\t" +
//                     //ellapsedDAGTime + "\t" +
//                     RPLength*1.0/inputLength + "\t" +
//                     //ellapsedRPTime + "\t" +
//                     RDAGLength*1.0/inputLength + "\n"
//                     //ellapsedRDAGTime + "\n" //+
//                     //proofFile + "\n"
//      writer.write(thisLine, 0, thisLine.length)
//    }
//    writer.close
//  }
//  
//  def compareCompressionAlgorithms(algorithms: List[Proof => Proof], measure: Proof => Int, directory: String, proofFiles: List[String], outputFilename: String) = {
//    val writer = new FileWriter(directory + outputFilename)
//    val runtime = Runtime.getRuntime()
//    for (proofFile <- proofFiles) {
//      println(proofFile)
//      try {
//        println("parsing")
//        val p0 = removeUnusedResolvents(proofCompression.ProofParser.getProofFromFile(directory + proofFile + ".proof"))
//
//        println("outputting proof with a single root")
//        proofCompression.ProofExporter.writeProofToFile(p0, proofFile + "(SingleRoot).proof")
//
//        val inputMeasure = measure(p0)
//        val outputMeasures = for (a <- algorithms) yield {
//          println("forcing garbage collection")
//          runtime.gc
//          println("duplicating")
//          val p = p0.duplicate
//          println("running")
//          val newP = a(p)
//          println("measuring output")
//          val m = measure(newP)
//          println((inputMeasure*1.0 - m)/inputMeasure)
//          m
//        }   
//
//        val compressionRates = ("" /: outputMeasures.map(m => "\t" + (inputMeasure*1.0 - m)/inputMeasure))((s1, s2) => s1 + s2)
//
//
//        val thisLine = inputMeasure +
//                      compressionRates +
//                      "\n"
//        println(thisLine)
//        writer.write(thisLine, 0, thisLine.length)
//      } catch {
//        case e => {throw e; println(proofFile); e.printStackTrace}
//      }
//    }
//    writer.close
//  }
//
//  def compareTwoCompressionAlgorithms(algorithm1: Proof => Proof, algorithm2: Proof => Proof, measure: Proof => Int, directory: String, proofFiles: List[String], outputFilename: String) = {
//    val writer = new FileWriter(directory + outputFilename)
//    for (proofFile <- proofFiles) {
//      println(proofFile)
//      try {
//        println("parsing")
//        val p0 = proofCompression.ProofParser.getProofFromFile(directory + proofFile + ".proof")
//        println("duplicating")
//        val p1 = p0.duplicate
//        println("duplicating")
//        val p2 = p0.duplicate
//        val inputMeasure = measure(p1)
//
//        println("running first algorithm")
//        val p1Out = algorithm1(p1)
//        val output1Measure = measure(p1Out)
//
//        println("running second algorithm")
//        val p2Out = algorithm2(p2)
//        val output2Measure = measure(p2Out)
//
//        val thisLine = inputMeasure + "\t" +
//                       (inputMeasure*1.0 - output1Measure)/inputMeasure + "\t" +
//                       (inputMeasure*1.0 - output2Measure)/inputMeasure + "\n"
//        println(thisLine)
//        writer.write(thisLine, 0, thisLine.length)
//      } catch {
//        case e => {throw e; println(proofFile); e.printStackTrace}
//      }
//    }
//    writer.close
//  }
//
//  def runRecyclePivots(directory: String, proofFiles: List[String], outputFilename: String) = {
//    val writer = new FileWriter(directory + outputFilename)
//    for (proofFile <- proofFiles) {
//      println(proofFile)
//      try {
//        println("parsing")
//        val startParsingTime = System.nanoTime
//        val p0 = proofCompression.ProofParser.getProofFromFile(directory + proofFile + ".proof")
//        val ellapsedParsingTime = (System.nanoTime - startParsingTime)/1000
//        println("duplicating")
//        val p1 = p0.duplicate
//        println("duplicating")
//        val p2 = p0.duplicate
//        val inputLength = p1.length
//
//        println("recycle pivots")
//        val startRPTime = System.nanoTime
//        recyclePivots(p1)
//        fix(p1)
//        val ellapsedRPTime = (System.nanoTime - startRPTime)/1000
//        val RPLength = p1.length
//
//        println("recycle pivots (improved)")
//        val startRPITime = System.nanoTime
//        recyclePivotsWithIntersection(p2)
//        fix(p2)
//        val ellapsedRPITime = (System.nanoTime - startRPITime)/1000
//        val RPILength = p2.length
//
//        val thisLine = inputLength + "\t" +
//                       (inputLength*1.0 - RPLength)/inputLength + "\t" +
//                       (inputLength*1.0 - RPILength)/inputLength + "\n"
//        println(thisLine)
//        writer.write(thisLine, 0, thisLine.length)
//      } catch {
//        case e => {throw e; println(proofFile); e.printStackTrace}
//      }
//    }
//    writer.close
//  }
//  
//  
//  
//  def runHypergraph(directory: String, proofFiles: List[String], outputFilename: String) = {
//    //val writer = new FileWriter(directory + outputFilename)
//    //val firstLine = "Filename \t\t\t" +
//                    "InputLength \t" +
//                    //"InputSize \t" +
//                    //"InputAverageNumberOfChildrenPerNode \t" +
//                    "ParsingTime \t\t" +
//                    "R_Length \t" +            // length after regularization
//                    "R_Time \t" +              // regularization time
//                    "DAG_Length \t" +          // length after DAGification
//                    "DAG_Time \t" +            // DAGification time
//                    "RP_Length \t" +           // length after pivot recycling
//                    "RP_Time \t" +             // pivot recycling time
//                    "R-DAG_Length \t" +        // length after regularization and DAGification
//                    "R-DAG_Time \t" +            // regularization and DAGification time
//                    "\n"
//    //writer.write(firstLine, 0, firstLine.length)
//    for (proofFile <- proofFiles) {
//      println(proofFile)
//      val startParsingTime = System.nanoTime
//      val p = proofCompression.ProofParser.getProofFromFile(directory + proofFile + ".proof").asInstanceOf[Resolvent].left
//      val ellapsedParsingTime = (System.nanoTime - startParsingTime)/1000
//      val inputLength = p.length
//
//      val startRTime = System.nanoTime
//      regularize(p)
//      fix(p)
//      val ellapsedRTime = (System.nanoTime - startRTime)/1000
//      val RLength = p.length
//
//      val startRDAGTime = System.nanoTime
//      DAGify(p, p => p.length)
//      val ellapsedRDAGTime = (System.nanoTime - startRDAGTime)/1000 + ellapsedRTime
//      val RDAGLength = p.length
//
//      val startHypergraphConstructionTime = System.nanoTime
//      val g = new ResolutionHypergraph(p)
//      val ellapsedHypergraphConstructionTime = (System.nanoTime - startHypergraphConstructionTime)/1000
//
//      //val gui = new HypergraphVisualizer
//      //gui.displayHypergraph(g)
//
//
//      val startHypergraphSimplificationTime = System.nanoTime
//      g.simplify
//      val ellapsedHypergraphSimplificationTime = (System.nanoTime - startHypergraphSimplificationTime)/1000
//      println(g.isTrivial)
//      val ReconstructedProofLength = g.getNodes.head.proof.length
//
//      val thisLine = inputLength + "\t" +
//                     ellapsedParsingTime + "\t" +
//                     RLength + "\t" +
//                     ellapsedRTime + "\t" +
//                     RDAGLength + "\t" +
//                     ellapsedRDAGTime + "\t" +
//                     ellapsedHypergraphConstructionTime + "\t" +
//                     ReconstructedProofLength + "\t" +
//                     ellapsedHypergraphSimplificationTime + "\t" +
//                     proofFile + "\n"
//      println(thisLine)
//
//      proofCompression.ProofExporter.writeProofToFile(g.getNodes.head.proof, directory + proofFile + "Reconstructed.proof")
//
//      //writer.write(thisLine, 0, thisLine.length)
//    }
//    //writer.close
//  }
  
}
