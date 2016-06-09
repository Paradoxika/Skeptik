package at.logic.skeptik.proof.sequent.resolution

import at.logic.skeptik.algorithm.unifier.MartelliMontanari
import at.logic.skeptik.expression.{E, Var}
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.algorithm.prover._

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

  implicit class UnitSequent(sequent: SeqSequent) { // FIXME: move this to some other place
    def literal: Literal =
      if (sequent.ant.size == 1 && sequent.suc.isEmpty) (sequent.ant.head, true)
      else if (sequent.ant.isEmpty && sequent.suc.size == 1) (sequent.suc.head, false)
      else throw new IllegalStateException("Given SeqSequent is not a unit")
  }

  implicit class LiteralsAreSequent(literals: Seq[Literal]) { // FIXME: move this to some other place
    def toSequent: SeqSequent = {
      val ant = literals.flatMap(l => if (l.negated) Some(l.unit) else None)
      val suc = literals.flatMap(l => if (l.negated) None else Some(l.unit))
      SeqSequent(ant: _*)(suc: _*)
    }
  }

  def unify(equations: Iterable[(E, E)])(implicit variables: mutable.Set[Var]) = MartelliMontanari(equations)

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

  override def auxFormulasMap: Map[SequentProofNode, SeqSequent] =
    unitClauses.zip(leftLiterals.map(_.toClause)).toMap + (clause -> rightLiterals.toSequent)

  override def conclusionContext: SeqSequent = clause.conclusion --* rightLiterals.toSequent

  override def mainFormulas: SeqSequent = SeqSequent()()

  override def premises: Seq[SequentProofNode] = clause +: unitClauses
}
