package at.logic.skeptik.algorithm.prover.actors

import akka.actor.{Actor, ActorLogging}
import akka.pattern.ask
import akka.util.Timeout
import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.algorithm.prover.actors.messages._
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.expression.Var
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.proof.sequent.conflictresolution.{Decision, UnitPropagationResolution}
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.{SequentProofNode, conflictresolution}

import scala.collection.mutable
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps

/**
  * @author Daniyar Itegulov
  */
class ConflictActor extends Actor with ActorLogging {
  private implicit val timeout: Timeout = 5 seconds

  private val clauseProof = mutable.Map.empty[Clause, SequentProofNode]

  val unifyingActor = context.actorSelection("../unify")
  val mainActor = context.actorSelection("../main")

  override def receive: Receive = {
    case Conflict(leftLiteral, rightLiteral, allClauses, decisions, reverseImpGraph) =>
      allClauses.foreach(clause => clauseProof(clause) = Axiom(clause.toSeqSequent))

      log.info(s"Conflict from $leftLiteral and $rightLiteral")

      /**
        * Finds conflict clause, used consisting of negation of all decisions-ancestors of `current`.
        *
        * @param current literal
        * @param substitution last instantiation of this literal
        * @return clause, representing disjunction of negated decision literals, used in propagation of current literal
        */
      def findConflictClause(current: Literal, substitution: Substitution = Substitution.empty): Clause = {
        if (allClauses contains current.toClause) {
          Clause.empty
        } else if (decisions contains current) {
          !substitution(current)
        } else if (reverseImpGraph contains current) {
          val conflictClauses = for ((clause, unifier) <- reverseImpGraph(current))
            yield unifier.map {
              case (lit, mgu) => findConflictClause(lit, mgu(substitution))
            }.fold(Clause.empty)(_ union _)
          conflictClauses.toSeq.sortBy(_.width).head
        } else {
          throw new IllegalStateException(s"Literal $current was propagated, but there is no history in implication graph")
        }
      }

      /**
        * Creates formal proof, which formally reasons `current` literal.
        *
        * @param current literal to be proved
        * @return formal proof, which conclusion is the `current`
        */
      def buildProof(current: Literal)(implicit variables: mutable.Set[Var]): SequentProofNode = {
        if (allClauses contains current.toClause) {
          Axiom(current.toClause.toSeqSequent)
        } else if (decisions contains current) {
          Decision(current.toClause)
        } else if (reverseImpGraph contains current) {
          val (clause, unifier) = reverseImpGraph(current).head
          val premiseProofs = unifier.map {
            case (lit, _) => buildProof(lit)
          }
          UnitPropagationResolution(premiseProofs, clauseProof(clause), current)
        } else {
          throw new IllegalStateException("Literal was propagated, but there is no history in implication graph")
        }
      }

      val variablesFuture = (unifyingActor ? GetVariables()).mapTo[Set[Var]]
      val future = (unifyingActor ? Unify(Seq(leftLiteral.unit), Seq(rightLiteral.unit)))
        .mapTo[Option[(Seq[Substitution], Substitution)]]

      Await.result(future.zip(variablesFuture), Duration.Inf) match {
        case (Some((Seq(leftMgu), rightMgu)), variables) =>
          implicit val vars = mutable.Set(variables.toSeq: _*)
          val conflictClauseLeft = findConflictClause(leftLiteral, leftMgu)
          val conflictClauseRight = findConflictClause(rightLiteral, rightMgu)
          val newClause = unique(conflictClauseLeft union conflictClauseRight)
          val conflictProof = conflictresolution.Conflict(buildProof(leftLiteral), buildProof(rightLiteral))
          clauseProof(newClause) = conflictresolution.ConflictDrivenClauseLearning(conflictProof)
          log.info(s"Derived conflict clause $newClause")
          mainActor ! Derived(newClause, reverseImpGraph, conflictProof)
        case _ =>
          log.error("leftLiteral and rightLiteral should be unifiable")
      }
    case other =>
      log.warning(s"Didn't expect, but got $other")
  }
}
