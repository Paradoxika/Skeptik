package at.logic.skeptik.algorithm.prover.actors

import akka.actor.{Actor, ActorLogging, ActorRef}
import akka.pattern.ask
import akka.util.Timeout
import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.algorithm.prover.actors.messages._
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.expression.substitution.immutable.Substitution

import scala.concurrent.Await
import scala.concurrent.duration._
import scala.language.postfixOps

/**
  * @author Daniyar Itegulov
  */
class ConflictActor(unifyingActor: ActorRef) extends Actor with ActorLogging {
  private implicit val timeout: Timeout = 2 seconds

  override def receive: Receive = {
    case Conflict(leftLiteral, rightLiteral, allClauses, decisions, reverseImpGraph) =>
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

      val future = (unifyingActor ? Unify(Seq(leftLiteral.unit), Seq(rightLiteral.unit)))
        .mapTo[Option[(Seq[Substitution], Substitution)]]

      val (Seq(leftMgu), rightMgu) = Await.result(future, Duration.Inf).get
      val conflictClauseLeft = findConflictClause(leftLiteral, leftMgu)
      val conflictClauseRight = findConflictClause(rightLiteral, rightMgu)
      val newClause = unique(conflictClauseLeft union conflictClauseRight)
      log.info(s"Derived conflict clause $newClause")
      sender ! Derived(newClause)
    case other =>
      log.warning(s"Didn't expect, but got $other")
  }
}
