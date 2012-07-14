package at.logic.skeptik.experiment.compression

import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.compressor.combinedRPILU._
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent.SequentProof
import at.logic.skeptik.parser._
import at.logic.skeptik.util.time._

object environment
extends MMap[String,String]

object Experimenter {

  // Measures

  object timeMeasure
  extends DoubleMeasure[Timed[_]]("%7.1f ms", _.time)

  object countMeasure
  extends Measure[Result] {
    var nb = 0
    var sum = MMap[String,Int]()

    def before(proof: Result) = { nb += 1 ; "" }

    def after(algorithm: String, proof: Result) = proof match {
      case c:CountedResult => 
        val value = c.count
        sum.update(algorithm, sum.getOrElse(algorithm,0) + value)
        value.toString + " times"
      case _ => ""
    }

    def average(algorithm: String) =
      if (sum(algorithm) != 0) String.format("%.1f times", double2Double(sum(algorithm).toDouble / nb.toDouble)) else ""
  }

  object compressionRatioMeasure
  extends IntPercentMeasure[Result](_.nodeCollection.size)

  val measures = List(timeMeasure, countMeasure, compressionRatioMeasure)

  // Algorithms

  val newUnitLowering = new SimpleAlgorithm ("new UL", NewUnitLowering)

  val newRP   = new SimpleAlgorithm("new  RP ", new RecyclePivots with outIntersection with LeftHeuristic)
  val newRPI  = new SimpleAlgorithm("opt  RPI", new RecyclePivots with Intersection with LeftHeuristic)
  val concRPI = new SimpleAlgorithm("conc RPI", new RecyclePivots with Intersection with MinConclusionHeuristic)
  val sizeRPI = new SimpleAlgorithm("size RPI", new RecyclePivots with Intersection with MinProofHeuristic)

  val newRPIr  = new RepeatAlgorithm("opt  RPI", new RecyclePivots with Intersection with LeftHeuristic)
  val sizeRPIr = new RepeatAlgorithm("size RPI", new RecyclePivots with Intersection with MinProofHeuristic)

  val newRPILU = new SimpleAlgorithm("new RPILU", { (p:SequentProof) =>
    (new RecyclePivots with Intersection with LeftHeuristic)(NewUnitLowering(p)) })
  val newLURPI = new SimpleAlgorithm("new LURPI", { (p:SequentProof) =>
    NewUnitLowering((new RecyclePivots with Intersection with LeftHeuristic)(p)) })
  val nLURPILU = new SimpleAlgorithm("nLURPILU", { (p:SequentProof) =>
    val lu = NewUnitLowering
    val rpi = new RecyclePivots with Intersection with LeftHeuristic
    lu(rpi(lu(p)))
  })

  val lowPsUn = new SimpleAlgorithm("low PsUn", new PseudoUnits(2))
  val lowPsU1 = new SimpleAlgorithm("low PsU1", new PseudoUnits(1))
  val onePsUn = new SimpleAlgorithm("one PsUn", new OnePassPseudoUnits(2))
  val onePsU1 = new SimpleAlgorithm("one PsU1", new OnePassPseudoUnits(1))

  val psunReg = new SimpleAlgorithm("PsUn Reg", new PseudoUnitsAfter(2))
  val psunOne = new SimpleAlgorithm("PsUn One", new PseudoUnitsAfter(1))
  val psunLow = new SimpleAlgorithm("PsUn Low", new PseudoUnitsBefore(2))
  val psunLo1 = new SimpleAlgorithm("PsUn Lo1", new PseudoUnitsBefore(1))

  val irunReg = new SimpleAlgorithm("IrUn Reg", new IrregularUnits with AlwaysRegularizeIrregularUnits)
  val irunLow = new SimpleAlgorithm("IrUn Low", new IrregularUnits with AlwaysLowerIrregularUnits     )

  val reMinReg = new SimpleAlgorithm("ReMinReg", new MinRegularizationEvaluation with DiscreteCollector with MinEval with MinRegularizationChoice)
  val reMinLow = new SimpleAlgorithm("ReMinLow", new MinRegularizationEvaluation with DiscreteCollector with MinEval with MinLoweringChoice)
  val reRegula = new SimpleAlgorithm("reRegula", new RegularizationEvaluation with QuadraticCollector with AddEval with RegularizeIfPossible)
  val reQuadra = new SimpleAlgorithm("reQuadra", new MinRegularizationEvaluation with QuadraticCollector with MinEval with MinLoweringChoice)

  val threeLow = new SimpleAlgorithm("3passLow", new ThreePassLower)

  val rednrec  = new SimpleAlgorithm("rednrec ", new ReduceAndReconstruct)
  val rednrec2 = new SimpleAlgorithm("rednrec2", new RRGrandPa)
  val rrnoa2   = new SimpleAlgorithm("rr no a2", new RRWithoutA2)

  val rednrecr = new TimeOutAlgorithm("rednrecr", new ReduceAndReconstruct)
  val rednre2r = new TimeOutAlgorithm("rednre2r", new RRGrandPa)
  val rrnoa2r  = new TimeOutAlgorithm("rr noa2r", new RRWithoutA2)

  val splitr   = new TimeOutAlgorithm("split R ", new Split with RandomChoice)
  val splitd   = new TimeOutAlgorithm("split D ", new Split with DeterministicChoice)

  val algorithms = Map(
    "UL"   -> newUnitLowering,
    "LU"   -> newUnitLowering,
    "RP"   -> newRP,
    "RPI"  -> newRPI,
    "cRPI"  -> concRPI,
    "sRPI"  -> sizeRPI,
    "RPIr" -> newRPIr,
    "sRPIr" -> sizeRPIr,
    "LURPI"-> newLURPI,
    "RPILU"-> newRPILU,
    "LURPILU" -> nLURPILU,
    "lowPsUn"  -> lowPsUn,
    "onePsU1"  -> onePsU1,
    "onePsUn"  -> onePsUn,
    "lowPsU1"  -> lowPsU1,
    "psUnReg"  -> psunReg,
    "psUnOne"  -> psunOne,
    "psUnLow"  -> psunLow,
    "psUnLo1"  -> psunLo1,
    "irUnReg"  -> irunReg,
    "irUnLow"  -> irunLow,
    "reMinReg" -> reMinReg,
    "reMinLow" -> reMinLow,
    "reRegula" -> reRegula,
    "reQuadra" -> reQuadra,
    "3passLow" -> threeLow,
    "rednrec"  -> rednrec,
    "rednrecr" -> rednrecr,
    "rednrec2" -> rednrec2,
    "rednre2r" -> rednre2r,
    "rrnoa2"   -> rrnoa2,
    "rrnoa2r"  -> rrnoa2r,
    "splitr"   -> splitr,
    "splitd"   -> splitd
  )

  def experiment(algos : Seq[WrappedAlgorithm], proofs : Seq[String]) =
  {
    // Algorithms
    for (proofFilename <- proofs) {
      // Read
      println("------------------------------------------------------------")
      print("* " + proofFilename)
      val proof = Result ( timed { (new SimplePropositionalResolutionProofFormatParser(proofFilename)).getProof } )
      for (measure <- measures) { print(" " + measure.before(proof)) }
      println()

      // Compress
      for (algo <- algos) {
        val compressed = algo(proof)
        print(algo.name + ": ")
        if (compressed.result.conclusion == proof.result.conclusion) {
          for (measure <- measures) { print(" " + measure.after(algo.name, compressed)) }
          println()
        }
        else
          println("Error, " + compressed.result.conclusion + " instead of " + proof.result.conclusion)
      }
    }

    // Report
    println("------------------------------------------------------------")
    println()
    println("------------------------------------------------------------")
    for (algo <- algos) {
      print(algo.name + ": ")
      for (measure <- measures) { print(" " + measure.average(algo.name)) }
      println()
    }
    println("------------------------------------------------------------")
  }

  def run(args: Array[String]): Unit =
  {
    val mapOptions = Map(
      "a" -> "algos",
      "t" -> "timeout"
    )

    var proofs = List[String]()
    var pos = 0
    while (pos < args.length)
      args(pos)(0) match {
        case '-' =>
          val key = args(pos).substring(1)
          environment.update(mapOptions.getOrElse(key,key), args(pos+1))
          pos += 2
        case _ =>
          proofs ::= args(pos)
          pos += 1
      }

    val algos = environment.getOrElse("algos","LU,RPI").split(",").map { algorithms(_) }
    experiment(algos, proofs)
  }
}
