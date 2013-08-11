package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.compressor.split._

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
    "RR" -> new ReduceAndReconstructTimeout(5000),
    "RRlm" -> new RRWithLowerMiddleTimeout(5000),
    "RRST" -> ReduceAndReconstructSimpleTermination,
    "RRCST" -> RRC1PSimpleTermination,
    "RRlmST" -> RRWithLowerMiddleSimpleTermination,
    "RRHST" -> RRWithHelsinkiSimpleTermination,
    "RROT" -> ReduceAndReconstructOverTermination,
    "RRCOT" -> RRC1POverTermination,
    "RRlmOT" -> RRWithLowerMiddleOverTermination,
    "RRHOT" -> RRWithHelsinkiOverTermination,
    "COT" -> C1POverTermination,
    "SOT" -> S1POverTermination,
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
