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
    algorithms(name.replace(' ','_')) = new TimeOutAlgorithm(String.format("%-8.8s",name), algo)

  addTimeOutAlgorithm("LU", NewUnitLowering)

  addTimeOutAlgorithm("RP",  RecyclePivots)
  addTimeOutAlgorithm("RPI", RecyclePivotsWithIntersection)

  addTimeOutAlgorithm("RPILU", IdempotentAlgorithm(RecyclePivotsWithIntersection, NewUnitLowering))
  addTimeOutAlgorithm("LURPI", IdempotentAlgorithm(NewUnitLowering, RecyclePivotsWithIntersection))

  addTimeOutAlgorithm("IU Reg", IrregularUnitsRegularize)
  addTimeOutAlgorithm("IU Low", IrregularUnitsLower)

  addTimeOutAlgorithm("RI Reg",   RegularizationInformationRegularizationChoice)
  addTimeOutAlgorithm("RI Low",   RegularizationEvaluationLoweringChoice)
  addTimeOutAlgorithm("RI alReg", RegularizationEvaluationRegularizeIfPossible)
  addTimeOutAlgorithm("RI Quad",  RegularizationEvaluationQuadraticHeuristic)

  addTimeOutAlgorithm("3pass LU", ThreePassLowerUnits)

  addTimeOutAlgorithm("LUniv",    LowerUnivalents)
  addTimeOutAlgorithm("LUnivRPI", LowerUnivalentsAfterRecyclePivots)
  addTimeOutAlgorithm("RPILUniv", LowerUnivalentsBeforeRecyclePivots)

  addTimeOutAlgorithm("RednRec", ReduceAndReconstruct)

  addTimeOutAlgorithm("Split",   Split)
  addTimeOutAlgorithm("TSplit R", TerminatingSplitRandom)
  addTimeOutAlgorithm("TSplit D", TerminatingSplitDeterministic)

  for (i <- 1 to 8) addTimeOutAlgorithm("MSplit" + i, new MultiSplit(i) with RandomChoice)

  addTimeOutAlgorithm("DAG",  DAGification)


  def getProofFromFile(filename: String) = ("""\.[^\.]+$""".r findFirstIn filename) match {
    case Some(".proof") => Result ( { (new SimplePropositionalResolutionProofFormatParser(filename)).getProof } )
    case Some(".smt2")  => Result ( { (new SMT2Parser(filename)).getProof } )
    case _ => throw new Exception("Unknown format for " + filename)
  }

  val initialMeasuresRecord = measures map { m => (m, 0.) }

  def csvReport(algos : Seq[WrappedAlgorithm], proofs : Seq[String], iteration: Int) =
  {
    for (proofFilename <- proofs) {

      // TODO: CSV header

      // Read
      print("\"" + proofFilename + "\"")
      val original = getProofFromFile(proofFilename)
      for (measure <- measures) print("," + measure(original))

      // Compress
      for (algo <- algos) {
        var measuresRecord = initialMeasuresRecord
        var i = 0
        do {
          val compressed = algo(original)
          measuresRecord = measuresRecord map { (t) => (t._1, t._2 + t._1(compressed)) }
          i += 1
        } while (i < iteration)

        for ((_, value) <- measuresRecord) print("," + (value / iteration))
      }

      println()
    }
  }

  def experiment(algos : Seq[WrappedAlgorithm], proofs : Seq[String]) =
  {
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
      "t" -> "timeout",
      "c" -> "csv"
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

    environment.get("csv") match {
      case Some(iteration) => csvReport(algos, proofs, iteration.toInt)
      case None            => experiment(algos, proofs)
    }
  }
}
