package at.logic.skeptik.algorithm.prover.conflict

import at.logic.skeptik.algorithm.prover.{Clause, _}
import at.logic.skeptik.algorithm.prover.util.DecisionLevel

/**
  * Very dumb algorithm, which just unions all literals on each decision level.
  *
  * @author Daniyar Itegulov
  */
object SimpleConflictAnalyser extends ConflictAnalyser{
  override def learnConflictClause(levels: Seq[DecisionLevel]): Clause =
    (Clause.empty /: levels.map(!_.literal)) (_ union _.toClause)
}
