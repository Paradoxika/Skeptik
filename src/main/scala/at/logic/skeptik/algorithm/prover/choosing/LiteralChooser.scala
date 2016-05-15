package at.logic.skeptik.algorithm.prover.choosing

import at.logic.skeptik.algorithm.prover.Literal
import at.logic.skeptik.algorithm.prover.structure.mutable.Cnf

/**
  * Represents general way to choose next literal.
  *
  * @author Daniyar Itegulov
  */
trait LiteralChooser {
  /**
    * Tries to choose best literal to make decision on.
    *
    * @param cnf which has some undecided literals
    * @return None, if all literals have decisions
    *         Some(literal), if literal should be decided
    */
  def chooseLiteral(cnf: Cnf): Option[Literal]
}
