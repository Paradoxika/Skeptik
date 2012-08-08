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
  extends DoubleMeasure[Result]("%7.1f ms", _.time)

  object countMeasure
  extends IntMeasure[Result](" times",_.count) {
    override def before(proof: Result) = { nb += 1 ; "" }

    override def after(algorithm: String, proof: Result) = {
      val value = proof.count
      sum.update(algorithm, sum.getOrElse(algorithm,0) + value)
      if (value > 1) value.toString + " times" else ""
    }
  } 

  object compressionRatioMeasure
  extends IntPercentMeasure[Result](_.proof.size)

  val measures = List(timeMeasure, countMeasure, compressionRatioMeasure)

  // Algorithms

  val algorithms = MMap[String, WrappedAlgorithm]()

  def addTimeOutAlgorithm(name: String, algo: CompressorAlgorithm[SequentProof]) =
    algorithms(name) = new TimeOutAlgorithm(String.format("%-8.8s",name), algo)

  addTimeOutAlgorithm("LU", NewUnitLowering)

//  val newRP    = new SimpleAlgorithm("RP      ", new RecyclePivots with outIntersection)
//  val newRPI   = new SimpleAlgorithm("RPI     ", new RecyclePivots with Intersection)
//
//  val newRPIr  = new RepeatAlgorithm("RPI rec ", new RecyclePivots with Intersection)
//
//  val newRPILU = new SimpleAlgorithm("RPILU   ", { (p:SequentProof) =>
//    (new RecyclePivots with Intersection)(NewUnitLowering(p)) })
//  val newLURPI = new SimpleAlgorithm("LURPI   ", { (p:SequentProof) =>
//    NewUnitLowering((new RecyclePivots with Intersection)(p)) })
//  val nLURPILU = new SimpleAlgorithm("LURPILU ", { (p:SequentProof) =>
//    val lu = NewUnitLowering
//    val rpi = new RecyclePivots with Intersection
//    lu(rpi(lu(p)))
//  })
//
//  val irunReg = new SimpleAlgorithm("IrUn Reg", new IrregularUnits with AlwaysRegularizeIrregularUnits)
//  val irunLow = new SimpleAlgorithm("IrUn Low", new IrregularUnits with AlwaysLowerIrregularUnits     )
//
//  val threeLow = new SimpleAlgorithm("3passLow", new ThreePassLower)
//
//  val reMinReg = new SimpleAlgorithm("ReMinReg", new RegularizationEvaluation with DiscreteCollector  with MinEval with MinRegularizationChoice)
//  val reMinLow = new SimpleAlgorithm("ReMinLow", new RegularizationEvaluation with DiscreteCollector  with MinEval with MinLoweringChoice)
//  val reRegula = new SimpleAlgorithm("reRegula", new RegularizationEvaluation with QuadraticCollector with AddEval with RegularizeIfPossible)
//  val reQuadra = new SimpleAlgorithm("reQuadra", new RegularizationEvaluation with QuadraticCollector with MinEval with MinLoweringChoice)
//
//  val rednrec  = new SimpleAlgorithm("rednrec ", new ReduceAndReconstruct)
//  val rednrec2 = new SimpleAlgorithm("rednrec2", new RRWithA2OnChild)
//  val rrnoa2   = new SimpleAlgorithm("rr no a2", new RRWithoutA2)
//
//  val rednrecr = new TimeOutAlgorithm("rednrecr", new ReduceAndReconstruct)
//  val rednre2r = new TimeOutAlgorithm("rednre2r", new RRWithA2OnChild)
//  val rrnoa2r  = new TimeOutAlgorithm("rr noa2r", new RRWithoutA2)
//
//  val splitr   = new TimeOutAlgorithm("split R ", new Split(false) with RandomChoice)
//  val splitd   = new TimeOutAlgorithm("split D ", new Split(false) with DeterministicChoice)

//    "UL"   -> newUnitLowering,
//    "LU"   -> newUnitLowering,
//    "RP"   -> newRP,
//    "RPI"  -> newRPI,
//    "RPIr" -> newRPIr,
//    "LURPI"-> newLURPI,
//    "RPILU"-> newRPILU,
//    "LURPILU" -> nLURPILU,
//    "irUnReg"  -> irunReg,
//    "irUnLow"  -> irunLow,
//    "3passLow" -> threeLow,
//    "reMinReg" -> reMinReg,
//    "reMinLow" -> reMinLow,
//    "reRegula" -> reRegula,
//    "reQuadra" -> reQuadra,
//    "LUniv"    -> new SimpleAlgorithm("LUniv   ", new LowerUnivalents),
//    "LUnivRPI" -> new SimpleAlgorithm("LUnivRPI", new LowerUnivalentsAfterRecyclePivots),
//    "RPILUniv" -> new SimpleAlgorithm("RPILUniv", new LowerUnivalentsBeforeRecyclePivots),
//    "rednrec"  -> rednrec,
//    "rednrecr" -> rednrecr,
//    "rednrec2" -> rednrec2,
//    "rednre2r" -> rednre2r,
//    "rrnoa2"   -> rrnoa2,
//    "rrnoa2r"  -> rrnoa2r,
//    "splitr"   -> splitr,
//    "splitd"   -> splitd,
//    "splitr1"  -> new TimeOutAlgorithm("split R1", new Split(true) with RandomChoice),
//    "splitd1"  -> new TimeOutAlgorithm("split D1", new Split(true) with DeterministicChoice),
//    "splitr1f" -> new RepeatAlgorithm("split R1", new Split(true) with RandomChoice),
//    "splitd1f" -> new RepeatAlgorithm("split D1", new Split(true) with DeterministicChoice),
//    "DAG"      -> new SimpleAlgorithm("DAG     ", DAGification)
//  ) ++
//  (1 to 8).map { n => val name = "msplitd"+n ; name -> new TimeOutAlgorithm(name, new MultiSplit(n) with DeterministicChoice) } ++
//  (1 to 8).map { n => val name = "msplitr"+n ; name -> new TimeOutAlgorithm(name, new MultiSplit(n) with RandomChoice) }

  def getProofFromFile(filename: String) = ("""\.[^\.]+$""".r findFirstIn filename) match {
    case Some(".proof") => Result ( { (new SimplePropositionalResolutionProofFormatParser(filename)).getProof } )
    case Some(".smt2")  => Result ( { (new SMT2Parser(filename)).getProof } )
    case _ => throw new Exception("Unknown format for " + filename)
  }  

  def experiment(algos : Seq[WrappedAlgorithm], proofs : Seq[String]) =
  {
    // Algorithms
    for (proofFilename <- proofs) {
      // Read
      println("------------------------------------------------------------")
      print("* " + proofFilename)
      val original = getProofFromFile(proofFilename)
      for (measure <- measures) { print(" " + measure.before(original)) }
      println()

      // Compress
      for (algo <- algos) {
        val compressed = algo(original)
//        println(compressed)
        print(algo.name + ": ")
        if (compressed.proof.root.conclusion == original.proof.root.conclusion) {
          for (measure <- measures) { print(" " + measure.after(algo.name, compressed)) }
          println()
        }
        else
          println("Error, " + compressed.proof.root.conclusion + " instead of " + original.proof.root.conclusion)
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
