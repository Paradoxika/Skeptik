package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor.combinedRPILU._

object Algorithms {
  val get = Map( 
    "LU" -> LowerUnits,
    "RP" -> RecyclePivots,
    "RPI" -> RecyclePivotsWithIntersection,
    "RPI[3]LU" -> IdempotentThreePassLowerUnits,
    "LUniv" -> LowerUnivalents,
    "LUnivRPI" -> IdempotentLowerUnivalentsAfterRecyclePivots,
    "RPI[3]LUniv" -> IdempotentLowerUnivalentsBeforeRecyclePivots,
    "R&Re" -> ReduceAndReconstruct,
    "Split" -> Split
  )
}