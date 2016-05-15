package at.logic.skeptik.algorithm.prover.util

import at.logic.skeptik.judgment.immutable.UnitSequent

import scala.collection.mutable

/**
  * Represents decision level.
  * Contains all information, needed to do a backtracking.
  *
  * @author Daniyar Itegulov
  */
class DecisionLevel(val literal: UnitSequent,
                    val varAssessment: mutable.Set[UnitSequent] = mutable.Set.empty,
                    val flipped: Boolean = false) // flipped == true means this literal was processed
                                                  // two times with different decisions.
