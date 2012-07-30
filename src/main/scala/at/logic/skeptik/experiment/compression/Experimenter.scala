package at.logic.skeptik.experiment.compression

import Array.canBuildFrom
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.compressor.combinedRPILU._
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.oldResolution.{Proof => OldProof}
import at.logic.skeptik.proof.sequent.SequentProof
import at.logic.skeptik.parser._


// I don't know if this factory should be in that file. Measure.scala is really generic...
class MeasurerFactory private (oldM: Measure[OldProof],
                               seqM: Measure[SequentProof])
{
  def oldMeasurer(p: OldProof)     = Measurer(oldM, p)
  def seqMeasurer(p: SequentProof) = Measurer(seqM, p)
}

object MeasurerFactory {
  def apply(measures: List[String], environment: Map[String,String]) =
    // Todo
    new MeasurerFactory(
      PercentMeasure("ratio", (p: OldProof) =>
        at.logic.skeptik.proof.oldResolution.defs.length(p).toDouble),
      PercentMeasure("ratio", (p: SequentProof) =>
        ProofNodeCollection(p).size.toDouble)
      )
}

object WrappedAlgorithmFactory {
    
  def SimpleOldAlgorithm(name: String, fct: (OldProof) => OldProof) = (env: Map[String,String]) =>
      WrappedOldAlgorithm(name, fct)
  def SimpleSequentAlgorithm(name: String, fct: SequentProof => SequentProof)= (env: Map[String,String]) =>
//      WrappedSequentAlgorithm(name, fct)
      WrappedSequentAlgorithm(name, { (p:SequentProof) => val r = fct(p) ; println(r.conclusion) ; r})

  def RepeatOldAlgorithm(name: String, fct: (OldProof) => OldProof) = (env: Map[String,String]) =>
      RepeatingOldAlgorithm(name, fct)
  def RepeatSequentAlgorithm(name: String, fct: (SequentProof) => SequentProof)= (env: Map[String,String]) =>
      RepeatingSequentAlgorithm(name, fct)

  val oldUnitLowering = SimpleOldAlgorithm ("old UL", UnitLowering.lowerUnits _)
  val newUnitLowering = SimpleSequentAlgorithm ("new UL", NewUnitLowering)

  val oldRecyclePivot = SimpleOldAlgorithm ("old RP",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivots(p)))
  val oldRPWithInters = SimpleOldAlgorithm ("old  RPI",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivotsWithIntersection(p)))
  val oldRPILU        = SimpleOldAlgorithm ("old RPILU",
        (p:OldProof) => ProofFixing.fix(Regularization.recyclePivotsWithIntersection(UnitLowering.lowerUnits(p))))
  val oldLURPI        = SimpleOldAlgorithm ("old LURPI",
        (p:OldProof) => UnitLowering.lowerUnits(ProofFixing.fix(Regularization.recyclePivotsWithIntersection(p))))

  val newRP   = SimpleSequentAlgorithm("new  RP ", new RecyclePivots with outIntersection with LeftHeuristic)
  val newRPI  = SimpleSequentAlgorithm("opt  RPI", new RecyclePivots with Intersection with LeftHeuristic)
  val concRPI = SimpleSequentAlgorithm("conc RPI", new RecyclePivots with Intersection with MinConclusionHeuristic)
  val sizeRPI = SimpleSequentAlgorithm("size RPI", new RecyclePivots with Intersection with MinProofHeuristic)

  val oldRPIr  = RepeatOldAlgorithm("old  RPI",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivotsWithIntersection(p)))
  val newRPIr  = RepeatSequentAlgorithm("opt  RPI", new RecyclePivots with Intersection with LeftHeuristic)
  val sizeRPIr = RepeatSequentAlgorithm("size RPI", new RecyclePivots with Intersection with MinProofHeuristic)

  val newRPILU = SimpleSequentAlgorithm("new RPILU", { (p:SequentProof) =>
    (new RecyclePivots with Intersection with LeftHeuristic)(NewUnitLowering(p)) })
  val newLURPI = SimpleSequentAlgorithm("new LURPI", { (p:SequentProof) =>
    NewUnitLowering((new RecyclePivots with Intersection with LeftHeuristic)(p)) })
  val nLURPILU = SimpleSequentAlgorithm("nLURPILU", { (p:SequentProof) =>
    val lu = NewUnitLowering
    val rpi = new RecyclePivots with Intersection with LeftHeuristic
    lu(rpi(lu(p)))
  })

  val lowPsUn = SimpleSequentAlgorithm("low PsUn", new PseudoUnits(2))
  val lowPsU1 = SimpleSequentAlgorithm("low PsU1", new PseudoUnits(1))
  val onePsUn = SimpleSequentAlgorithm("one PsUn", new OnePassPseudoUnits(2))
  val onePsU1 = SimpleSequentAlgorithm("one PsU1", new OnePassPseudoUnits(1))

  val psunReg = SimpleSequentAlgorithm("PsUn Reg", new PseudoUnitsAfter(2))
  val psunOne = SimpleSequentAlgorithm("PsUn One", new PseudoUnitsAfter(1))
  val psunLow = SimpleSequentAlgorithm("PsUn Low", new PseudoUnitsBefore(2))
  val psunLo1 = SimpleSequentAlgorithm("PsUn Lo1", new PseudoUnitsBefore(1))

  val irunReg = SimpleSequentAlgorithm("IrUn Reg", new IrregularUnits with AlwaysRegularizeIrregularUnits)
  val irunLow = SimpleSequentAlgorithm("IrUn Low", new IrregularUnits with AlwaysLowerIrregularUnits     )

  val reMinReg = SimpleSequentAlgorithm("ReMinReg", new MinRegularizationEvaluation with DiscreteCollector with MinEval with MinRegularizationChoice)
  val reMinLow = SimpleSequentAlgorithm("ReMinLow", new MinRegularizationEvaluation with DiscreteCollector with MinEval with MinLoweringChoice)
  val reRegula = SimpleSequentAlgorithm("reRegula", new RegularizationEvaluation with QuadraticCollector with AddEval with RegularizeIfPossible)
  val reQuadra = SimpleSequentAlgorithm("reQuadra", new MinRegularizationEvaluation with QuadraticCollector with MinEval with MinLoweringChoice)

  val threeLow = SimpleSequentAlgorithm("3passLow", new ThreePassLower)

  val allAlgos = List(
    oldUnitLowering,
    newUnitLowering,
    oldRecyclePivot,
    oldRPWithInters,
    oldRPILU,
    oldLURPI
  )

  val algosMap = Map(
    "UL"    -> oldUnitLowering,
    "LU"    -> oldUnitLowering,
    "nUL"   -> newUnitLowering,
    "nLU"   -> newUnitLowering,
    "RP"    -> oldRecyclePivot,
    "nRP"   -> newRP,
    "RPI"   -> oldRPWithInters,
    "nRPI"  -> newRPI,
    "RPIUL" -> oldRPILU,
    "RPILU" -> oldRPILU,
    "ULRPI" -> oldLURPI,
    "LURPI" -> oldLURPI,
    "cRPI"  -> concRPI,
    "sRPI"  -> sizeRPI,
    "RPIr"  -> oldRPIr,
    "nRPIr" -> newRPIr,
    "sRPIr" -> sizeRPIr,
    "nLURPI"-> newLURPI,
    "nRPILU"-> newRPILU,
    "nLURPILU" -> nLURPILU,
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
    "3passLow" -> threeLow
  )

  def apply(env: Map[String,String]):List[WrappedAlgorithm] =
      env.getOrElse("algos","").split(",").map(name => algosMap(name)(env)).toList
}

object Experimenter {

  def experiment(algos : List[WrappedAlgorithm],
                 proofs : List[String],
                 environment : Map[String,Any],
                 measurerFactory : MeasurerFactory
                 ) =
  {
    var oldProof : OldProof = null
    var oldMeasurer : Measurer[OldProof] = DumbMeasurer
    var sequentProof : SequentProof = null
    var sequentMeasurer : Measurer[SequentProof] = DumbMeasurer

    // Initialisation
    def proofsKind(acc: (Boolean, Boolean), lst: List[WrappedAlgorithm]) : (Boolean, Boolean) =
      acc match {
        case (true, true) => acc
        case (prop, seq) =>
          lst match {
            case Nil => acc
            case (_:WrappedOldAlgorithm)::q => proofsKind((true, seq), q)
            case (_:WrappedSequentAlgorithm)::q => proofsKind((prop, true), q)
          }
        }
    val (hasPropositional, hasSequent) = proofsKind((false, false), algos)

    // Algorithms
    for (proofFilename <- proofs) {
      println("------------------------------------------------------------")
      print("* " + proofFilename)
      val beginParsing = java.lang.System.currentTimeMillis
      if (hasPropositional) {
        // TODO: add timer and output
        oldProof =
          ProofParser.getProofFromFile(proofFilename)
        oldMeasurer = measurerFactory.oldMeasurer(oldProof)
      }
      if (hasSequent) {
        // TODO: add timer and output
        sequentProof = 
          (new SimplePropositionalResolutionProofFormatParser(proofFilename)).getProof
        sequentMeasurer = measurerFactory.seqMeasurer(sequentProof)
      }
      println(String.format(" (%.2f s)", double2Double((java.lang.System.currentTimeMillis - beginParsing)/1000.0)))

      algos.foreach( _ match {
        case a: WrappedOldAlgorithm     => a.experiment(oldProof,     oldMeasurer)
        case a: WrappedSequentAlgorithm => a.experiment(sequentProof, sequentMeasurer)
      })
    }

    // Report
    println("------------------------------------------------------------")
    println()
    println("------------------------------------------------------------")
    algos.foreach(println(_))
    println("------------------------------------------------------------")
  }

  def run(args: Array[String]): Unit =
  {
    val mapOptions = Map(
      "a" -> "algos"
    )

    def parseArgs(pos: Int, env: Map[String,String], proofs: List[String])
    : (Map[String,String], List[String]) = {
      if (pos >= args.length)
        (env, proofs)
      else args(pos)(0) match {
        case '-' =>
          val key = args(pos).substring(1)
          parseArgs(pos+2, env + (mapOptions.getOrElse(key,key) -> args(pos+1)), proofs)
        case _ =>
          parseArgs(pos+1, env, args(pos)::proofs)
      }
    }

    val (env, proofs) = parseArgs(0, Map[String,String]("algos" -> "UL,RPI"), Nil)

    val measurerFactory = MeasurerFactory(List(), env)
    val algos = WrappedAlgorithmFactory(env)

    experiment(algos, proofs, env, measurerFactory)
  }
}
