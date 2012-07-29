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
      if ((sum contains algorithm) && sum(algorithm) != 0) String.format("%.1f times", double2Double(sum(algorithm).toDouble / nb.toDouble)) else ""
  }

  object compressionRatioMeasure
  extends IntPercentMeasure[Result](_.nodeCollection.size)

  val measures = List(timeMeasure, countMeasure, compressionRatioMeasure)

  // Algorithms

  val newUnitLowering = new SimpleAlgorithm ("UnitLowr", NewUnitLowering)

  val newRP   = new SimpleAlgorithm("new  RP ", new RecyclePivots with outIntersection)
  val newRPI  = new SimpleAlgorithm("opt  RPI", new RecyclePivots with Intersection)

  val newRPIr  = new RepeatAlgorithm("opt  RPI", new RecyclePivots with Intersection)

  val newRPILU = new SimpleAlgorithm("new RPILU", { (p:SequentProof) =>
    (new RecyclePivots with Intersection)(NewUnitLowering(p)) })
  val newLURPI = new SimpleAlgorithm("new LURPI", { (p:SequentProof) =>
    NewUnitLowering((new RecyclePivots with Intersection)(p)) })
  val nLURPILU = new SimpleAlgorithm("nLURPILU", { (p:SequentProof) =>
    val lu = NewUnitLowering
    val rpi = new RecyclePivots with Intersection
    lu(rpi(lu(p)))
  })

  val lowPsUn = new SimpleAlgorithm("low PsUn", new PseudoUnits(2))
  val lowPsU1 = new SimpleAlgorithm("low PsU1", new PseudoUnits(1))

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
  val rednrec2 = new SimpleAlgorithm("rednrec2", new RRWithA2OnChild)
  val rrnoa2   = new SimpleAlgorithm("rr no a2", new RRWithoutA2)

  val rednrecr = new TimeOutAlgorithm("rednrecr", new ReduceAndReconstruct)
  val rednre2r = new TimeOutAlgorithm("rednre2r", new RRWithA2OnChild)
  val rrnoa2r  = new TimeOutAlgorithm("rr noa2r", new RRWithoutA2)

  val splitr   = new TimeOutAlgorithm("split R ", new Split(false) with RandomChoice)
  val splitd   = new TimeOutAlgorithm("split D ", new Split(false) with DeterministicChoice)

  val algorithms = Map(
    "UL"   -> newUnitLowering,
    "LU"   -> newUnitLowering,
    "RP"   -> newRP,
    "RPI"  -> newRPI,
    "RPIr" -> newRPIr,
    "LURPI"-> newLURPI,
    "RPILU"-> newRPILU,
    "LURPILU" -> nLURPILU,
    "lowPsUn"  -> lowPsUn,
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
    "splitd"   -> splitd,
    "splitr1"  -> new TimeOutAlgorithm("split R1", new Split(true) with RandomChoice),
    "splitd1"  -> new TimeOutAlgorithm("split D1", new Split(true) with DeterministicChoice),
    "splitr1f" -> new RepeatAlgorithm("split R1", new Split(true) with RandomChoice),
    "splitd1f" -> new RepeatAlgorithm("split D1", new Split(true) with DeterministicChoice),
    "DAG"      -> new SimpleAlgorithm("DAG     ", DAGification),
    "splitDAG" -> new TimeOutAlgorithm("SplitDAG", { p => DAGification((new MultiSplit(1) with DeterministicChoice)(p)) }),
    "DAGps"    -> new SimpleAlgorithm("DAGps   ", { p => DAGification((new PseudoUnitsAfter(1))(p)) }),
    "psDAG"    -> new SimpleAlgorithm("psDAG   ", { p => (new PseudoUnitsAfter(1))(DAGification(p)) }),
    "tstspl"   -> new SimpleAlgorithm("tst spl ", { p => (new Split(false) with DeterministicChoice)(DAGification(p)) }),
    "tstms1"   -> new SimpleAlgorithm("tst ms1 ", { p => (new MultiSplit(1) with DeterministicChoice)(DAGification(p)) }),
    "tstms3"   -> new SimpleAlgorithm("tst ms3 ", { p => (new MultiSplit(3) with DeterministicChoice)(DAGification(p)) }),
    "tstspld"  -> new SimpleAlgorithm("tst spld", { p => DAGification((new Split(false) with DeterministicChoice)(DAGification(p))) }),
    "tstms1d"  -> new SimpleAlgorithm("tst ms1d", { p => DAGification((new MultiSplit(1) with DeterministicChoice)(DAGification(p))) }),
    "tstms3d"  -> new SimpleAlgorithm("tst ms3d", { p => DAGification((new MultiSplit(3) with DeterministicChoice)(DAGification(p))) })
  ) ++
  (1 to 8).map { n => val name = "msplitd"+n ; name -> new TimeOutAlgorithm(name, new MultiSplit(n) with DeterministicChoice) } ++
  (1 to 8).map { n => val name = "msplitr"+n ; name -> new TimeOutAlgorithm(name, new MultiSplit(n) with RandomChoice) }

  def getProofFromFile(filename: String) = ("""\.[^\.]+$""".r findFirstIn filename) match {
    case Some(".proof") => Result ( timed { (new SimplePropositionalResolutionProofFormatParser(filename)).getProof } )
    case Some(".smt2")  => Result ( timed { (new SMT2Parser(filename)).getProof } )
    case _ => throw new Exception("Unknown format for " + filename)
  }  

  def experiment(algos : Seq[WrappedAlgorithm], proofs : Seq[String]) =
  {
    // Algorithms
    for (proofFilename <- proofs) {
      // Read
      println("------------------------------------------------------------")
      print("* " + proofFilename)
      val proof = getProofFromFile(proofFilename)
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
