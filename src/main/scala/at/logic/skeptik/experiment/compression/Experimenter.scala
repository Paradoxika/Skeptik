package at.logic.skeptik.experiment.compression

import collection.mutable.{HashMap => MMap, HashSet => MSet}
import collection.immutable.{HashSet => ISet}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.compressor.combinedRPILU._
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.parser._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._

object environment
extends MMap[String,String]

object Experimenter {

  // Measures

  object timeMeasure
  extends DoubleMeasure[Result]("%7.1f ms", _.time)

  object countMeasure
  extends IntMeasure[Result](" times",_.count) {
    override def before(proof: Result) = { nb += 1 ; "" }
  } 

  object nodeCompressionRatioMeasure
  extends IntPercentMeasure[Result](_.proof.size)

  object axiomCompressionRatioMeasure
  extends IntPercentMeasure[Result](_.nbAxioms)

  object variableCompressionRatioMeasure
  extends IntPercentMeasure[Result](_.nbVariables)

  object axiomSizeCompressionRatioMeasure
  extends IntPercentMeasure[Result](_.axiomsSize)

  object literalsCompressionRatioMeasure
  extends IntPercentMeasure[Result](_.nbLiterals)

  object estimatedVerificationTimeCompressionRatioMeasure
  extends DoublePercentMeasure[Result](_.estimatedVerificationTime)

  object irregularNodeCompressionRatioMeasure
  extends IntPercentMeasure[Result]( { result =>
    var nbIrregularNodes = 0
    def visit(node: SequentProofNode, childrenPivots: Seq[ISet[E]]) =
      node match {
        case CutIC(_,_,pivot,_) if !childrenPivots.isEmpty =>
          var pivots = childrenPivots.tail.foldLeft(childrenPivots.head) (_ ++ _)
          if (pivots contains pivot) { nbIrregularNodes += 1 ; pivots } else pivots + pivot
        case _ => ISet[E]()
      }
    result.proof.bottomUp(visit)
    nbIrregularNodes
  })


  val measures = List(timeMeasure, countMeasure,
                      nodeCompressionRatioMeasure,
                      axiomCompressionRatioMeasure, variableCompressionRatioMeasure,
                      literalsCompressionRatioMeasure, estimatedVerificationTimeCompressionRatioMeasure)
//                      axiomSizeCompressionRatioMeasure,
//                      irregularNodeCompressionRatioMeasure)

  // Algorithms

  val algorithms = MMap[String, WrappedAlgorithm]()

  def addTimeOutAlgorithm(name: String, algo: CompressorAlgorithm[SequentProofNode]) =
    algorithms(name.replace(' ','_')) = new TimeOutAlgorithm(String.format("%-10.10s",name), algo)

  addTimeOutAlgorithm("LU", NewUnitLowering)

  addTimeOutAlgorithm("RP",  RecyclePivots)
  addTimeOutAlgorithm("RPI", IdempotentRecyclePivotsWithIntersection)

  addTimeOutAlgorithm("RPILU", IdempotentAlgorithm(IdempotentRecyclePivotsWithIntersection, NewUnitLowering))
  addTimeOutAlgorithm("LURPI", IdempotentAlgorithm(NewUnitLowering, IdempotentRecyclePivotsWithIntersection))

  addTimeOutAlgorithm("IU Reg", IdempotentIrregularUnitsRegularize)
  addTimeOutAlgorithm("IU Low", IdempotentIrregularUnitsLower)

  addTimeOutAlgorithm("RI Reg",   IdempotentRegularizationInformationRegularizationChoice)
  addTimeOutAlgorithm("RI Low",   IdempotentRegularizationEvaluationLoweringChoice)
  addTimeOutAlgorithm("RI alReg", IdempotentRegularizationEvaluationRegularizeIfPossible)
  addTimeOutAlgorithm("RI Quad",  IdempotentRegularizationEvaluationQuadraticHeuristic)

  addTimeOutAlgorithm("3pass LU", IdempotentThreePassLowerUnits)

  addTimeOutAlgorithm("LUniv",    LowerUnivalents)
  addTimeOutAlgorithm("LUniv Op", LowerUnivalentsOpt)
  addTimeOutAlgorithm("LUnivRPI", IdempotentLowerUnivalentsAfterRecyclePivots)
  addTimeOutAlgorithm("LUvRPI Op",IdempotentLowerUnivalentsAfterRecyclePivotsOpt)
  addTimeOutAlgorithm("RPILUniv", IdempotentLowerUnivalentsBeforeRecyclePivots)

  addTimeOutAlgorithm("RednRec", ReduceAndReconstruct)

  addTimeOutAlgorithm("Split",   Split)
  addTimeOutAlgorithm("TSplit R", TerminatingSplitRandom)
  addTimeOutAlgorithm("TSplit D", TerminatingSplitDeterministic)

  for (i <- 1 to 8) addTimeOutAlgorithm("MSplit" + i, new MultiSplit(i) with RandomChoice)

  addTimeOutAlgorithm("DAG",  DAGification)

  // Test for practical idempotency
  addTimeOutAlgorithm("RPI R",      RecyclePivotsWithIntersection)
  addTimeOutAlgorithm("RPILU R",    RepeatableWhileCompressingAlgorithm(RecyclePivotsWithIntersection, NewUnitLowering))
  addTimeOutAlgorithm("LURPI R",    RepeatableWhileCompressingAlgorithm(NewUnitLowering, RecyclePivotsWithIntersection))
  addTimeOutAlgorithm("RPILUniv R", LowerUnivalentsBeforeRecyclePivots)
  addTimeOutAlgorithm("LUnivRPI R", LowerUnivalentsAfterRecyclePivots)

  def getProofNodeFromFile(filename: String) = ("""\.[^\.]+$""".r findFirstIn filename) match {
    case Some(".proof") => Result ( { (new SimplePropositionalResolutionProofNodeFormatParser(filename)).getProofNode } )
    case Some(".smt2")  => Result ( { (new SMT2Parser(filename)).getProofNode } )
    case _ => throw new Exception("Unknown format for " + filename)
  }

  val initialMeasuresRecord = measures map { m => (m, 0.0) }

  def csvReport(algos : Seq[WrappedAlgorithm], proofs : Seq[String], iteration: Int) =
  {
    for (proofFilename <- proofs) {

      // TODO: CSV header

      // Read
      print("\"" + proofFilename + "\"")
      val original = getProofNodeFromFile(proofFilename)
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
      val original = getProofNodeFromFile(proofFilename)
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
