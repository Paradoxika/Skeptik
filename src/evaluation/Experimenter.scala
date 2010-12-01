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
      val startParsingTime = System.nanoTime
      val p1 = ProofParser.getProofFromFile(directory + proofFile + ".proof")
      val ellapsedParsingTime = (System.nanoTime - startParsingTime)/1000
      val p2 = p1.duplicate
      val p3 = p1.duplicate
      val inputLength = proofLength(p1)

      val startRTime = System.nanoTime
      regularize(p1)
      fixProof(p1)
      val ellapsedRTime = (System.nanoTime - startRTime)/1000
      val RLength = proofLength(p1)

      val startRDAGTime = System.nanoTime
      DAGify(p1)
      println(isRegular(p1))
      val ellapsedRDAGTime = (System.nanoTime - startRDAGTime)/1000 + ellapsedRTime
      val RDAGLength = proofLength(p1)

      val startDAGTime = System.nanoTime
      DAGify(p2)
      //println(isRegular(p2))
      val ellapsedDAGTime = (System.nanoTime - startDAGTime)/1000
      val DAGLength = proofLength(p2)

      val startRPTime = System.nanoTime
      recyclePivot(p3)
      fixProof(p3)
      println(isRegular(p3))
      println()
      val ellapsedRPTime = (System.nanoTime - startRPTime)/1000
      val RPLength = proofLength(p3)

      val thisLine = inputLength + "\t" +
                     ellapsedParsingTime + "\t" +
                     RLength*1.0/inputLength + "\t" +
                     ellapsedRTime + "\t" +
                     DAGLength*1.0/inputLength + "\t" +
                     ellapsedDAGTime + "\t" +
                     RPLength*1.0/inputLength + "\t" +
                     ellapsedRPTime + "\t" +
                     RDAGLength*1.0/inputLength + "\t" +
                     ellapsedRDAGTime + "\n" //+
                     //proofFile + "\n"
      writer.write(thisLine, 0, thisLine.length)
    }
    writer.close
  }
}
