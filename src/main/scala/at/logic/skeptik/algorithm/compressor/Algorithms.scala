package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor.split._

object Algorithms {
  val get = Map( 
    "LU" -> LowerUnits,
    "RP" -> RecyclePivots,
    "RPI" -> RecyclePivotsWithIntersection,
    "RPI[3]LU" -> IdempotentThreePassLowerUnits,
    "LUniv" -> LowerUnivalents,
    "LUnivRPI" -> IdempotentLowerUnivalentsAfterRecyclePivots,
    "RPI[3]LUniv" -> LowerUnivalentsBeforeRecyclePivots,
    "R&R" -> new ReduceAndReconstruct(5000),
    "CottonSplit" -> new CottonSplit(30000),
    "RandomBoudouSplit" -> new RandomBoudouSplit(30000),
    "DeterministicBoudouSplit" -> new DeterministicBoudouSplit(30000),
    "MultiSplit2" -> new TimeoutMultiSplit(2,5000),
    "MultiSplit3" -> new TimeoutMultiSplit(3,5000),
    "MultiSplit4" -> new TimeoutMultiSplit(4,5000),
    "DAGify" -> DAGify
  )
}