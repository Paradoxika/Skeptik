package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor.split.RandomBoudouSplit

import at.logic.skeptik.algorithm.compressor.split.DeterministicBoudouSplit

import at.logic.skeptik.algorithm.compressor.split.CottonSplit

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
    "DAGify" -> DAGify
  )
}