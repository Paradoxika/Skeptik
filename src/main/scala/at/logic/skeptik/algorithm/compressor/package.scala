package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.compressor.split._
import at.logic.skeptik.algorithm.compressor.reduceAndReconstruct._

// Algorithm names should contain only alphanumeric characters

// ToDo: the name of an algorithm should be a property defined in the algorithm's class

package object compressor {
  val algorithms = Map(
    "DAGify" -> DAGify,
    "ET" -> EliminateTautologies,
    "RU" -> RecycleUnits,
    "RP" -> RecyclePivots,
    "RPI" -> RecyclePivotsWithIntersection,
    "RPC" -> RecyclePivotsWithConclusionSequent,
    "LU" -> LowerUnits,
    "LUniv" -> LowerUnivalents,
    "RPI3LU" -> IdempotentThreePassLowerUnits,
    "LUnivRPI" -> IdempotentLowerUnivalentsAfterRecyclePivots,
    "RPI3LUniv" -> LowerUnivalentsBeforeRecyclePivots,

    "RR" -> new ReduceAndReconstructS1P(5000),
    "RRC" -> new ReduceAndReconstructC1P(5000),
    "RRlm" -> new ReduceAndReconstructMiddleLowerTimeout(5000),
    "RRH" -> new ReduceAndReconstructHelsinkiTimeout(5000),
    "RRST" -> RRS1PSimpleTermination,
    "RRCST" -> RRC1PSimpleTermination,
    "RRlmST" -> RRMiddleLowerSimpleTermination,
    "RRHST" -> RRHelsinkiSimpleTermination,
    "RROT" -> RRS1POverTermination,
    "RRCOT" -> RRC1POverTermination,
    "RRlmOT" -> RRMiddleLowerOverTermination,
    "RRHOT" -> RRHelsinkiOverTermination,
    "RRROT" -> RRS1PRandomA2,
    "RRCROT" -> RRC1PRandomA2,
    "RRlmROT" -> RRMiddleLowerRandomA2,
    "RRHROT" -> RRHelsinkiRandomA2,

    "Split" -> new CottonSplit(30000),
    "RBSplit" -> new RandomBoudouSplit(30000),
    "DBSplit" -> new DeterministicBoudouSplit(30000),
    "MSplit2" -> new TimeoutMultiSplit(2,5000),
    "MSplit3" -> new TimeoutMultiSplit(3,5000),
    "MSplit4" -> new TimeoutMultiSplit(4,5000),
    "FWS" -> FWS,
    "BWSt" -> BWSt,
    "BWSm" -> BWSm
  )
}
