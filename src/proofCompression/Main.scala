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
  def main(args: Array[String]): Unit = {

//    val gui = new HypergraphVisualizer
//    gui.displayHypergraph(g3)

    CADEExperiments.run()

//    for ((benchmarkSet,benchmarkSetName) <- benchmarks) {
//      Experimenter.compareCompressionAlgorithms(List(p => lowerUnits(p),
//                                                     p => fixTopDown(recyclePivots(p)),
//                                                     p => fixTopDown(recyclePivotsWithIntersection(p)),
//                                                     p => fix(recyclePivotsWithIntersection(lowerUnits(p))),
//                                                     p => lowerUnits(fix(recyclePivotsWithIntersection(p)))
//                                                    ),
//                                                p => p.length,
//                                                directorySatRace, benchmarkSet, "Length-LU-RP-RPI-RPILU-RPILUDag - " + benchmarkSetName + " - " + System.currentTimeMillis() + ".txt")
//    }


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
