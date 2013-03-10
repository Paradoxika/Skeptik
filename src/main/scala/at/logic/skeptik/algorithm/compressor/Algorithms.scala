package at.logic.skeptik.algorithm.compressor

object Algorithms {
  val get = Map( 
    "LU" -> LowerUnits,
    "RP" -> RecyclePivots,
    "RPI" -> RecyclePivotsWithIntersection,
    "RPI[3]LU" -> IdempotentThreePassLowerUnits,
    "LUniv" -> LowerUnivalents,
    "LUnivRPI" -> IdempotentLowerUnivalentsAfterRecyclePivots,
    "RPI[3]LUniv" -> IdempotentLowerUnivalentsBeforeRecyclePivots,
    "R&R" -> ReduceAndReconstruct,
    "Split" -> Split,
    "DAGify" -> DAGify
  )
}