package at.logic.skeptik.algorithm.compressor

object Algorithms {
  val get = Map( 
    "LU" -> LowerUnits,
    "RP" -> RecyclePivots,
    "RPI" -> RecyclePivotsWithIntersection,
    "RPI[3]LU" -> IdempotentThreePassLowerUnits,
    "LUniv" -> LowerUnivalents,
    "LUnivRPI" -> IdempotentLowerUnivalentsAfterRecyclePivots,
    "RPI[3]LUniv" -> LowerUnivalentsBeforeRecyclePivots,
    "R&R" -> ReduceAndReconstruct,
    "CottonSplit" -> new CottonSplit(30000),
    "RandomBoudouSplit" -> new RandomBoudouSplit(30000),
    "DeterministicBoudouSplit" -> new DeterministicBoudouSplit(30000),
    "DAGify" -> DAGify
  )
}