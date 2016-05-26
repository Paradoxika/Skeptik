package at.logic.skeptik.algorithm.prover.util

import at.logic.skeptik.algorithm.prover.Literal

import scala.collection.mutable

/**
  * Represents decision level.
  * Contains all information, needed to do a backtracking.
  *
  * @author Daniyar Itegulov
  */
class DecisionLevel(val literal: Literal,
                    val varAssessment: mutable.Set[Literal] = mutable.Set.empty)
