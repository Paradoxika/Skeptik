package at.logic.skeptik.proof.sequent.resolution

import at.logic.skeptik.algorithm.unifier.MartelliMontanari
import at.logic.skeptik.expression.{E, Var}
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal

import scala.collection.mutable

/**
  * Represents Unit-Propagation Resolution rule from Conflict Resolution calculus.
  *
  * @author Daniyar Itegulov
  */
class UnitPropagationResolution(val clause: SequentProofNode, // right premise
                                val unitClauses: Seq[SequentProofNode], // left premises
                                val leftLiterals: Seq[Literal], //
                                val rightLiterals: Seq[Literal])
                               (implicit unifiableVariables: mutable.Set[Var]) extends SequentProofNode {

  def unify(equations: Iterable[(E, E)]) = MartelliMontanari(equations)

  require(unitClauses.forall(_.conclusion.width == 1), "All unitClauses should be unit")
  require(leftLiterals.size == rightLiterals.size, "Should have as much leftLiterals as rightLiterals")
  require(unitClauses.size == leftLiterals.size, "Should have as much unitClauses as leftLiterals")
  require(unitClauses.size == rightLiterals.size, "Should have as much unitClauses as rightLiterals")
  require(clause.conclusion.width == unitClauses.size + 1, "Right clause should have one literal more than unitClauses")
  require(leftLiterals.zip(rightLiterals).forall { case (f, s) => f == !s }, "Right literals and left literals should be opposite")

  val leftAux = leftLiterals.map(_.unit)
  val rightAux = rightLiterals.map(_.unit)

  val mgu = unify(leftAux.zip(rightAux)) match {
    case None => throw new Exception("Unit-Propagation Resolution: given premise clauses are not resolvable")
    case Some(u) => u
  }

  override def auxFormulasMap: Map[SequentProofNode, SeqSequent] = ???

  override def conclusionContext: SeqSequent = ???

  override def mainFormulas: SeqSequent = SeqSequent()()

  override def premises: Seq[SequentProofNode] = clause +: unitClauses
}
