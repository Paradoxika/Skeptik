package ResK.evaluation

import ResK.calculi._
import ResK.calculi.resolution.{Proof => OldProof, _}
import ResK.proofs._
import ResK.algorithms._


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
        ResK.calculi.resolution.measures.length(p).toDouble),
      PercentMeasure("ratio", (p: SequentProof) =>
        ProofNodeCollection(p).size.toDouble)
      )
}

object WrappedAlgorithmFactory {
    
  def SimpleOldAlgorithm(name: String, fct: (OldProof) => OldProof) = (env: Map[String,String]) =>
      WrappedOldAlgorithm(name, fct)
  def SimpleSequentAlgorithm(name: String, fct: (SequentProof) => SequentProof)= (env: Map[String,String]) =>
      WrappedSequentAlgorithm(name, fct)

  def RepeatOldAlgorithm(name: String, fct: (OldProof) => OldProof) = (env: Map[String,String]) =>
      RepeatingOldAlgorithm(name, fct)
  def RepeatSequentAlgorithm(name: String, fct: (SequentProof) => SequentProof)= (env: Map[String,String]) =>
      RepeatingSequentAlgorithm(name, fct)

  val oldUnitLowering = SimpleOldAlgorithm ("old UL", UnitLowering.lowerUnits _)
  val newUnitLowering = SimpleSequentAlgorithm ("new UL", NewUnitLowering)

  val oldRecyclePivot = SimpleOldAlgorithm ("old RP",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivots(p)))
//  val newRecyclePivot = SimpleSequentAlgorithm ("new RP", RecyclePivots)
  val oldRPWithInters = SimpleOldAlgorithm ("old  RPI",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivotsWithIntersection(p)))
//  val newRPWithInters = SimpleSequentAlgorithm ("new RPI", RecyclePivotsWithIntersection)
  val oldRPILU        = SimpleOldAlgorithm ("old RPILU",
        (p:OldProof) => ProofFixing.fix(Regularization.recyclePivotsWithIntersection(UnitLowering.lowerUnits(p))))
//  val newRPILU        = SimpleSequentAlgorithm ("new RPILU",
//        (p:SequentProof) => RecyclePivotsWithIntersection(NewUnitLowering(p)))
  val oldLURPI        = SimpleOldAlgorithm ("old LURPI",
        (p:OldProof) => UnitLowering.lowerUnits(ProofFixing.fix(Regularization.recyclePivotsWithIntersection(p))))
//  val newLURPI        = SimpleSequentAlgorithm ("new LURPI",
//        (p:SequentProof) => NewUnitLowering(RecyclePivotsWithIntersection(p)))

  val leftRPI = SimpleSequentAlgorithm("left RPI", new RecyclePivots with Intersection with LeftHeuristic)
  val concRPI = SimpleSequentAlgorithm("conc RPI", new RecyclePivots with Intersection with MinConclusionHeuristic)
  val sizeRPI = SimpleSequentAlgorithm("size RPI", new RecyclePivots with Intersection with MinProofHeuristic)

  val oldRPIr  = RepeatOldAlgorithm ("old  RPI r",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivotsWithIntersection(p)))
  val leftRPIr = RepeatSequentAlgorithm("left RPI r", new RecyclePivots with Intersection with LeftHeuristic)
  val concRPIr = RepeatSequentAlgorithm("conc RPI r", new RecyclePivots with Intersection with MinConclusionHeuristic)
  val sizeRPIr = RepeatSequentAlgorithm("size RPI r", new RecyclePivots with Intersection with MinProofHeuristic)

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
//    "nRP"   -> newRecyclePivot,
    "RPI"   -> oldRPWithInters,
//    "nRPI"  -> newRPWithInters,
    "RPIUL" -> oldRPILU,
    "RPILU" -> oldRPILU,
    "ULRPI" -> oldLURPI,
    "LURPI" -> oldLURPI,
//    "nRPIUL" -> newRPILU,
//    "nRPILU" -> newRPILU,
//    "nULRPI" -> newLURPI,
//    "nLURPI" -> newLURPI
    "lRPI" -> leftRPI,
    "cRPI" -> concRPI,
    "sRPI" -> sizeRPI,
    "RPIr"  -> oldRPIr,
    "lRPIr" -> leftRPIr,
    "cRPIr" -> concRPIr,
    "sRPIr" -> sizeRPIr
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
          (new ResK.parsers.SimplePropositionalResolutionProofFormatParser(proofFilename)).getProof
        sequentMeasurer = measurerFactory.seqMeasurer(sequentProof)
      }
      println(String.format(" (%.2f s)", double2Double((java.lang.System.currentTimeMillis - beginParsing)/1000.)))

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

  def main(args: Array[String]): Unit =
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
