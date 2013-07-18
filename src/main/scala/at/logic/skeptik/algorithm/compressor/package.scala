package at.logic.skeptik.algorithm

import at.logic.skeptik.algorithm.compressor.split._

// Algorithm names should contain only alphanumeric characters
// otherwise, the command line parser does not work.

package object compressor {
  val algorithms = Map(
    "RPI" -> RecyclePivotsWithIntersection,
    "LU" -> LowerUnits,
    "RP" -> RecyclePivots,
    "RPI3LU" -> IdempotentThreePassLowerUnits,
    "LUniv" -> LowerUnivalents,
    "LUnivRPI" -> IdempotentLowerUnivalentsAfterRecyclePivots,
    "RPI3LUniv" -> LowerUnivalentsBeforeRecyclePivots,
    "RedRec" -> new ReduceAndReconstruct(5000),
    "CottonSplit" -> new CottonSplit(30000),
    "RandomBoudouSplit" -> new RandomBoudouSplit(30000),
    "DeterministicBoudouSplit" -> new DeterministicBoudouSplit(30000),
    "MultiSplit2" -> new TimeoutMultiSplit(2,5000),
    "MultiSplit3" -> new TimeoutMultiSplit(3,5000),
    "MultiSplit4" -> new TimeoutMultiSplit(4,5000),
    "DAGify" -> DAGify,
    "EliminateTautologies" -> EliminateTautologies,
    "FWS" -> FWS,
    "BWSt" -> BWSt,
    "BWSm" -> BWSm,
    "RU" -> RecycleUnits,
    "RPC" -> RecyclePivotsWithConclusionSequent
  )
}