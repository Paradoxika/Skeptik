/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package evaluation

import scala.collection.mutable._
import proofCompression.Utilities._
import proofCompression.ResolutionCalculus._
import proofCompression.Hypergraph._
import proofCompression.GUI._
import proofCompression.ProofRegularization._
import proofCompression.ProofDAGification._
import proofCompression._
import java.io.FileWriter

object Experimenter {

  def runHypergraph(directory: String, proofFiles: List[String], outputFilename: String) = {
    //val writer = new FileWriter(directory + outputFilename)
    //val firstLine = "Filename \t\t\t" +
                    "InputLength \t" +
                    //"InputSize \t" +
                    //"InputAverageNumberOfChildrenPerNode \t" +
                    "ParsingTime \t\t" +
                    "R_Length \t" +            // length after regularization
                    "R_Time \t" +              // regularization time
                    "DAG_Length \t" +          // length after DAGification
                    "DAG_Time \t" +            // DAGification time
                    "RP_Length \t" +           // length after pivot recycling
                    "RP_Time \t" +             // pivot recycling time
                    "R-DAG_Length \t" +        // length after regularization and DAGification
                    "R-DAG_Time \t" +            // regularization and DAGification time
                    "\n"
    //writer.write(firstLine, 0, firstLine.length)
    for (proofFile <- proofFiles) {
      println(proofFile)
      val startParsingTime = System.nanoTime
      val p = ProofParser.getProofFromFile(directory + proofFile + ".proof").asInstanceOf[Resolvent].left
      val ellapsedParsingTime = (System.nanoTime - startParsingTime)/1000
      val inputLength = proofLength(p)

      val startRTime = System.nanoTime
      regularize(p)
      fixProof(p)
      val ellapsedRTime = (System.nanoTime - startRTime)/1000
      val RLength = proofLength(p)

      val startRDAGTime = System.nanoTime
      DAGify(p)
      val ellapsedRDAGTime = (System.nanoTime - startRDAGTime)/1000 + ellapsedRTime
      val RDAGLength = proofLength(p)

      val startHypergraphConstructionTime = System.nanoTime
      val g = new ResolutionHypergraph(p)
      val ellapsedHypergraphConstructionTime = (System.nanoTime - startHypergraphConstructionTime)/1000

      //val gui = new HypergraphVisualizer
      //gui.displayHypergraph(g)


      val startHypergraphSimplificationTime = System.nanoTime
      g.simplify
      val ellapsedHypergraphSimplificationTime = (System.nanoTime - startHypergraphSimplificationTime)/1000
      println(g.isTrivial)
      val ReconstructedProofLength = proofLength(g.getNodes.head.proof)

      val thisLine = inputLength + "\t" +
                     ellapsedParsingTime + "\t" +
                     RLength + "\t" +
                     ellapsedRTime + "\t" +
                     RDAGLength + "\t" +
                     ellapsedRDAGTime + "\t" +
                     ellapsedHypergraphConstructionTime + "\t" +
                     ReconstructedProofLength + "\t" +
                     ellapsedHypergraphSimplificationTime + "\t" +
                     proofFile + "\n"
      println(thisLine)

      ProofExporter.writeProofToFile(g.getNodes.head.proof, directory + proofFile + "Reconstructed.proof")

      //writer.write(thisLine, 0, thisLine.length)
    }
    //writer.close
  }

  def run(directory: String, proofFiles: List[String], outputFilename: String) = {
    val writer = new FileWriter(directory + outputFilename)
    val firstLine = "Filename \t\t\t" +
                    "InputLength \t" +
                    //"InputSize \t" +
                    //"InputAverageNumberOfChildrenPerNode \t" +
                    "ParsingTime \t\t" +
                    "R_Length \t" +            // length after regularization
                    "R_Time \t" +              // regularization time
                    "DAG_Length \t" +          // length after DAGification
                    "DAG_Time \t" +            // DAGification time
                    "RP_Length \t" +           // length after pivot recycling
                    "RP_Time \t" +             // pivot recycling time
                    "R-DAG_Length \t" +        // length after regularization and DAGification
                    "R-DAG_Time \t" +            // regularization and DAGification time
                    "\n"
    //writer.write(firstLine, 0, firstLine.length)
    for (proofFile <- proofFiles) {
      println(proofFile)
      println("parsing")
      val startParsingTime = System.nanoTime
      val p0 = ProofParser.getProofFromFile(directory + proofFile + ".proof")
      val ellapsedParsingTime = (System.nanoTime - startParsingTime)/1000
      val p1 = p0.duplicate
      val p2 = p0.duplicate
      val p3 = p0.duplicate
      val inputLength = proofLength(p1)

      println("regularizing")
      val startRTime = System.nanoTime
      regularize(p1)
      fixProof(p1)
      val ellapsedRTime = (System.nanoTime - startRTime)/1000
      val RLength = proofLength(p1)

      println("removing new sinks")
      val p4 = removeUnusedResolvents(p1)


      println("DAGifying")
      val startRDAGTime = System.nanoTime
      DAGify(p4)
      val ellapsedRDAGTime = (System.nanoTime - startRDAGTime)/1000 + ellapsedRTime
      val RDAGLength = proofLength(p4)
      //println("DAGified")

      println("DAGifying the original proof")
      val startDAGTime = System.nanoTime
      DAGify(p2)
      //println(isRegular(p2))
      val ellapsedDAGTime = (System.nanoTime - startDAGTime)/1000
      val DAGLength = proofLength(p2)

      println("recycle pivots")
      val startRPTime = System.nanoTime
      recyclePivot(p3)
      fixProof(p3)
      val ellapsedRPTime = (System.nanoTime - startRPTime)/1000
      val RPLength = proofLength(p3)
      

      val thisLine = inputLength + "\t" +
                     //ellapsedParsingTime + "\t" +
                     RLength*1.0/inputLength + "\t" +
                     //ellapsedRTime + "\t" +
                     DAGLength*1.0/inputLength + "\t" +
                     //ellapsedDAGTime + "\t" +
                     RPLength*1.0/inputLength + "\t" +
                     //ellapsedRPTime + "\t" +
                     RDAGLength*1.0/inputLength + "\n"
                     //ellapsedRDAGTime + "\n" //+
                     //proofFile + "\n"
      writer.write(thisLine, 0, thisLine.length)
    }
    writer.close
  }
}
