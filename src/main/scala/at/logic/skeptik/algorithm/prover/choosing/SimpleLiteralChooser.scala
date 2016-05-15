package at.logic.skeptik.algorithm.prover.choosing

import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.algorithm.prover.structure.mutable.Cnf

/**
  * Very dumb algorithm, which just pick some random undecided variable.
  *
  * @author Daniyar Itegulov
  */
object SimpleLiteralChooser extends LiteralChooser {
  override def chooseLiteral(cnf: Cnf): Option[Literal] =
    cnf.variables.find(variable =>
      !cnf.assessment.contains(variable) && !cnf.assessment.contains(!variable)
    ).map(varToLit(_))
}
