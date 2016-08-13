package at.logic.skeptik.algorithm.prover.actors.messages

import at.logic.skeptik.algorithm.prover.Clause

/**
  * @author Daniyar Itegulov
  */
case class Reset(allClauses: Seq[Clause])
