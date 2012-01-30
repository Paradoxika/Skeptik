package ResK.evaluation

import ResK.algorithms.Regularization._
import ResK.algorithms.DAGification._
import ResK.algorithms.ProofFixing._
import ResK.algorithms.UnitLowering._
import ResK.calculi.resolution.measures._

object CADEExperiments {
    
  def run() = {  
    val dir = "/Users/Bruno/Documents/proofs/"
    val directory = dir + "BWPProofs/"
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


      val directory2 = dir + "SmallProofs/"
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


    val directorySatRace = dir + "SatRace2010/"
    val proofFilesSoftVerificationNecBigger = List(
                             "10-U-15228(SingleRoot)",
                             "14-U-15228",
                             "15-U-10652",
                             "18-U-10652"
                          ).map(s => "software-verification/nec/hard-" + s)

      val proofFilesSoftVerificationNecSmaller = List(
                             "2-U-9007(SingleRoot)",
                             "15-U-8013(SingleRoot)",
                             "10-U-9007(SingleRoot)",
                             "6-U-7061(SingleRoot)",
                             "12-U-7061(SingleRoot)"
                          ).map(s => "software-verification/nec/hard-" + s)

    val proofFilesSoftVerificationNecSmallerThan3MB = List(
                             "9-U-10652(SingleRoot)",
                             "13-U-9007(SingleRoot)"
                          ).map(s => "software-verification/nec/hard-" + s)


    val proofFilesSoftVerificationNecSmallerThan2MB = List(
                             "11-U-7061(SingleRoot)",
                             "25-U-7061(SingleRoot)",
                             "2-U-10652(SingleRoot)",
                             "7-U-10652(SingleRoot)",
                             "0-U-7061(SingleRoot)"
                          ).map(s => "software-verification/nec/hard-" + s)

    val proofFilesSoftVPost = List("zfcp(SingleRoot)"
                          ).map(s => "software-verification/post/" + s)

    val proofFilesSoftVBabic = List("dspam_dump_vc972(SingleRoot)"
                          ).map(s => "software-verification/babic/" + s)


    val proofFilesHardVIBM = List("45(SingleRoot)",
                             "100(SingleRoot)"
                          ).map(s => "hardware-verification/ibm/SAT_dat.k" + s)

    val proofFilesHardVManolios = List("c8idw_s(SingleRoot)",
                             "c10ni_s(SingleRoot)",
                             "f6bid(SingleRoot)"
                          ).map(s => "hardware-verification/manolios/" + s)


    val benchmarks = List(//(proofFilesHardVManolios, "HardVManolios"),
                          //(proofFilesSoftVPost, "SoftVPost"),
                          //(proofFilesSoftVBabic, "SoftVBabic"),
                          //(proofFilesHardVIBM, "HardVIBM"),
                          //(proofFilesSoftVerificationNecSmallerThan2MB, "SoftVNecSmallerThan2MB"),
                          //(proofFilesSoftVerificationNecSmallerThan3MB, "SoftVNecSmallerThan3MB-9-U")
                          //(proofFilesSoftVerificationNecSmaller, "SoftVNecSmaller"),
                          //(proofFilesSoftVerificationNecBigger, "SoftVNecBigger"),
                          (proofFilesAim, "AIM")
                          //(proofFilesJNH, "JNH"),
                          //(proofFilesBF, "BF"),
                          //(proofFilesDubois,"Dubois"),
                          //(proofFilesPret,"Pret"),
                          //(proofFilesSSA,"SSA")
                          //(proofFilesPigeonHole,"Pigeon")
                         )

    for ((benchmarkSet,benchmarkSetName) <- benchmarks) {
      Experimenter.run(List(("LU", p => lowerUnits(p)),
                               ("RP", p => fixTopDown(recyclePivots(p))),
                               ("RPI", p => fixTopDown(recyclePivotsWithIntersection(p))),
                               ("RPILU", p => fix(recyclePivotsWithIntersection(lowerUnits(p)))),
                               ("LURPI", p => lowerUnits(fix(recyclePivotsWithIntersection(p))))
                              ),
                          p => length(p),
                          //directorySatRace,
                          directory2,
                          benchmarkSet,
                          "Length-LU-RP-RPI-RPILU-LURPI - " + benchmarkSetName + " - " + System.currentTimeMillis() + ".txt")
    }
  }
  
// This was the function used for the CADE Experiments...
  
//  def runCADE(algorithms: List[(String, Proof => Proof)], measure: Proof => Int, directory: String, proofFiles: List[String], outputFilename: String) = {
//    val writer = new FileWriter(directory + outputFilename)
//    val runtime = Runtime.getRuntime()
//    for (proofFile <- proofFiles) {
//      println(proofFile)
//      try {
//        println("parsing")
//        val p0 = removeUnusedResolvents(proofCompression.ProofParser.getProofFromFile(directory + proofFile + ".proof"))
//
//        println("outputting proof with a single root")
//        proofCompression.ProofExporter.writeProofToFile(p0, directory + proofFile + "(SingleRoot).proof")
//
//        val inputMeasure = measure(p0)
//        val outputMeasures = for (a <- algorithms) yield {
//          println("forcing garbage collection")
//          runtime.gc
//          println("duplicating")
//          val p = p0.duplicate
//          println("running " + a._1)
//          val startTime = System.nanoTime
//          val newP = a._2(p)
//          val time = (System.nanoTime - startTime)/1000000
//          println("exporting to file")
//          proofCompression.ProofExporter.writeProofToFile(newP, directory + proofFile + "(" + a._1 + ").proof")
//          println("measuring output")
//          val m = (measure(newP),time)
//          println((inputMeasure*1.0 - m._1)/inputMeasure)
//          println(time)
//          m
//        }
//
//        val compressionRatesAndTimes = ("" /: outputMeasures.map(m => "\t" + (inputMeasure*1.0 - m._1)/inputMeasure + "\t" + m._2 + "\t" + 1000.0*(inputMeasure*1.0 - m._1)/m._2))((s1, s2) => s1 + s2)
//
//
//        val thisLine = inputMeasure +
//                      compressionRatesAndTimes +
//                      "\n"
//        println(thisLine)
//        writer.write(thisLine, 0, thisLine.length)
//      } catch {
//        case e => {throw e; println(proofFile); e.printStackTrace}
//      }
//    }
//    writer.close
//  }
  
  
}
