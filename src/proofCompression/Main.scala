/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression


import scala.collection.mutable._
import proofCompression.Utilities._
import proofCompression.ResolutionCalculus._
import proofCompression.Hypergraph._
import proofCompression.GUI._
import proofCompression.Regularization._
import proofCompression.DAGification._
import proofCompression.ProofFixing._
import proofCompression._
import proofCompression.UnitLowering._
import evaluation._

object Main {
  /**
   * @param args the command line arguments
   */
  def main(args: Array[String]): Unit = {

//    val gui = new HypergraphVisualizer
//    gui.displayHypergraph(g3)
//

    val directory = "proofs/BWPProofs/"
    val proofFiles = List(//"ContractionAndSplittingCase1",
                          //"ContractionAndSplittingCase2",
                          //"ContractionAndSplittingCase3"
                          //"TheFirstChallenge1",
                          //"TheFirstChallenge",
                          //"pigeon(3)(2)",
                          //"DAGifiableTree",
                          //"SMT2010",
                          //"irregularWithProblematicLiterals",
                          //"irregularWithoutProblematicLiterals",
                          //"simple"
                          "TheFirstChallenge2"
                          )


    val directory2 = "proofs/SmallProofs/"
    val proofFilesAim = List("50-1_6-no-1",
                             "50-1_6-no-2",
                             "50-1_6-no-3",
                             "50-1_6-no-4",
                             "50-2_0-no-1",
                             "50-2_0-no-2",
                             "50-2_0-no-3",
                             "50-2_0-no-4",
                             "100-1_6-no-1",
                             "100-1_6-no-2",
                             "100-1_6-no-3",
                             "100-1_6-no-4",
                             "100-2_0-no-1",
                             "100-2_0-no-2",
                             "100-2_0-no-3",
                             "100-2_0-no-4",
                             "200-1_6-no-1",
                             "200-1_6-no-2",
                             "200-1_6-no-3",
                             "200-1_6-no-4",
                             "200-2_0-no-1",
                             "200-2_0-no-2",
                             "200-2_0-no-3",
                             "200-2_0-no-4"
                          ).map(s => "aim-" + s)

    val proofFilesPigeonHole = List("6", // Stack overflow during parsing after 1 minute
                              "7" // Stack Overflow during parsing after 51 seconds
                              //"8", // Stack Overflow during parsing after 1 minute 32 seconds
                             //"9" // Stack Overflow during parsing after 54 seconds
                          ).map(s => "hole" + s)

    val proofFilesDubois = List(
                             "20",
                             "21",
                             "22", // Stack overflow during regularization after about 6 minutes
                             "23",
                             "24",
                             "25",
                             "26", // Stack overflow during regularization after about 7 minutes
                             "27",
                             "28",
                             "29",
                             "30",
                             "50" // Stack overflow during regularization after about 7 minutes
                          ).map(s => "dubois" + s)

    val proofFilesJNH = List("2",
                             "3",
                             "4",
                             "5",
                             "6",  // runs for quite some time
                             "8",
                             "9",
                             "10",
                             "11",
                             "13",
                             "14",
                             "15",
                             "16", // Stack Overflow during Regularization after almost 10 minutes
                             "18",
                             "19",
                             "20",
                             "202",
                             "203",
                             "206", // Stack Overflow during Regularization after about 5 minutes
                             "208", // Stack Overflow during Regularization after about 6 minutes
                             "211",
                             "214",
                             "215",
                             "216",
                             "219",
                             "302",
                             "303",
                             "304",
                             "305",
                             "306", // Stack Overflow during Regularization after about 6 minutes
                             "307",
                             "308",
                             "309",
                             "310"
                          ).map(s => "jnh" + s)

    val proofFilesBF = List("0432-007", // Stack overflow during regularization after 3 minutes 35 seconds
                             "1355-075",
                             "1355-638",
                             "2670-001"
                          ).map(s => "bf" + s)

    val proofFilesPret = List("60_25",
                              "60_40",
                              "60_60",
                              "60_75",
                              "150_25", // Stack Overflow during Regularization after about 10 minutes
                              "150_40", // Stack Overflow
                              "150_60", // Stack Overflow
                              "150_75" // Stack Overflow
                          ).map(s => "pret" + s)

    val proofFilesSSA = List("0432-003",
                             "2670-130", // Stack overflow during regularization after about 5 minutes
                             "2670-141",  // Runs for too long... I interrupted after 13minutes...
                             "6288-047"
                          ).map(s => "ssa" + s)


    val directorySatRace = "proofs/SatRace2010/"
    val proofFilesSoftVerificationNec = List("0-U-7061",
                             "2-U-9007"
//                             "2-U-10652",
//                             "6-U-7061",
//                             "7-U-10652",
//                             "9-U-10652",
//                             "10-U-9007",
//                             "10-U-15228",
//                             "11-U-7061",
//                             "12-U-7061",
//                             "13-U-9007",
//                             "15-U-10652",
//                             "18-U-10652",
//                             "20-U-10652",
//                             "25-U-7061"
                          ).map(s => "software-verification/nec/hard-" + s)

//    Experimenter.runRecyclePivots(directory2, proofFilesAim, "RPI-outputAim" + System.currentTimeMillis() + ".txt")
//    Experimenter.runRecyclePivots(directory2, proofFilesJNH, "RPI-outputJNH20110106.txt")
//    Experimenter.runRecyclePivots(directory2, proofFilesBF, "RPI-outputBF20110106.txt")
//    Experimenter.runRecyclePivots(directory2, proofFilesDubois, "RPI-outputDubois20110106.txt")
//    Experimenter.runRecyclePivots(directory2, proofFilesPret, "RPI-outputPret20110106.txt")
//    Experimenter.runRecyclePivots(directory2, proofFilesSSA, "RPI-outputSSA20110106.txt")

    //Experimenter.runRecyclePivots(directorySatRace, proofFilesSoftVerificationNec, "RPI-outputSoftVerificationNec20110106.txt")

    //Experimenter.runRecyclePivots(directory2, proofFilesPigeonHole, "RPI-outputPigeon20110107.txt")

    val benchmarks = List((proofFilesAim, "Aim"),
                          (proofFilesJNH, "JNH"),
                          (proofFilesBF, "BF"),
                          (proofFilesDubois,"Dubois"),
                          (proofFilesPret,"Pret"),
                          (proofFilesSSA,"SSA")
                          //(proofFilesPigeonHole,"Pigeon")
                         )

    for ((benchmarkSet,benchmarkSetName) <- benchmarks) {
      Experimenter.compareCompressionAlgorithms(List(p => fix(recyclePivots(p)),
                                                     p => fix(recyclePivotsWithIntersection(p)),
                                                     p => lowerUnits(p),
                                                     p => fix(recyclePivotsWithIntersection(lowerUnits(p))),
                                                     p => DAGify(fix(recyclePivotsWithIntersection(lowerUnits(p))), p => p.length) ),
                                                p => p.length,
                                                directory2, benchmarkSet, "Length-RP-RPI-LU-RPILU-RPILUDag - " + benchmarkSetName + " - " + System.currentTimeMillis() + ".txt")
    }


    //Experimenter.run(directory2, proofFilesAim, "outputAim20101223.txt")
    //Experimenter.run(directory2, proofFilesPigeonHole, "outputPigeon20101223.txt")
    //Experimenter.run(directory2, proofFilesJNH, "outputJNH20101223.txt")
    //Experimenter.run(directory2, proofFilesBF, "outputBF20101223.txt")
    //Experimenter.run(directory2, proofFilesDubois, "outputDubois20101223.txt")
    //Experimenter.run(directory2, proofFilesPret, "outputPret20101223.txt")
    //Experimenter.run(directory2, proofFilesSSA, "outputSSA20101223.txt")
    //Experimenter.runHypergraph(directory2, proofFilesAim, "outputAimHypergraph20101208.txt")
    //Experimenter.runHypergraph(directory, proofFiles, "output.txt")

  }
}
