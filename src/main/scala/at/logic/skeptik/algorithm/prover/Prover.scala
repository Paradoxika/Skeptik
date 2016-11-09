package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.expression.Var
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode

import scala.collection.mutable

/**
  * @author Daniyar Itegulov
  */
trait Prover {
  def prove(cnf: CNF)(implicit variables: mutable.Set[Var]): Option[Proof[SequentProofNode]]
}
