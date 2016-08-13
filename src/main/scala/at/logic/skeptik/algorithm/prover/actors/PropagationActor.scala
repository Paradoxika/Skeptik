package at.logic.skeptik.algorithm.prover.actors

import akka.actor.{Actor, ActorLogging, ActorRef}
import akka.pattern.ask
import akka.util.Timeout

import scala.concurrent.duration._
import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.algorithm.prover.actors.messages._
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.expression.substitution.immutable.Substitution

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.concurrent.{Await, Future}
import scala.language.postfixOps

/**
  * @author Daniyar Itegulov
  */
class PropagationActor(unifyingActor: ActorRef) extends Actor with ActorLogging {
  @volatile
  private var unifiableUnits = Map.empty[Literal, Set[Literal]].withDefaultValue(Set.empty)
  // For each clause (or literal) what literals was produced from it
  @volatile
  private var reverseImplicationGraph =
    Map.empty[Literal, Set[(Clause, Seq[(Literal, Substitution)])]].withDefaultValue(Set.empty)
  // Literals which were decided
  private val decisions = ArrayBuffer.empty[Literal]
  // All clauses include initial and CDCL clauses
  @volatile
  private var allClauses = Seq.empty[Clause]
  // For each literal what initial clauses produced it
  private val ancestor = mutable.Map.empty[Literal, mutable.Set[Clause]].withDefaultValue(mutable.Set.empty)

  import context.dispatcher

  private implicit val timeout: Timeout = 2 seconds

  val mainActor = context.actorSelection("../main")

  /**
    * Check if `initial` is an ancestor of `initial` in implication graph.
    * @param current to check as a descendant
    * @param ancestor to check as an ancestor
    * @return true, if initial is ancestor of current
    *         false, otherwise
    */
  private def isAncestor(current: Literal, ancestor: Literal): Boolean = {
    if (current == ancestor) return true
    if (allClauses contains current.toClause) {
      false
    } else if (decisions contains current) {
      false
    } else {
      reverseImplicationGraph(current).exists {
        case (clause, unifiers) => unifiers.exists { case (lit, _) => isAncestor(lit, ancestor) }
      }
    }
  }

  override def receive: Receive = {
    case Resolve(clause) =>
      val unifyCandidates = clause.literals.map(unifiableUnits(_).toSeq)
      val futures = ArrayBuffer.empty[Future[Option[(Seq[Substitution], Substitution)]]]
      for (conclusionId <- unifyCandidates.indices) {
        // Id of literal which will be a conclusion
        val conclusion = clause.literals(conclusionId)
        // All unifiers excluding that one for conclusion
        val unifiers = unifyCandidates.take(conclusionId) ++ unifyCandidates.drop(conclusionId + 1)
        // All literals excluding conclusion
        val literals = clause.literals.take(conclusionId) ++ clause.literals.drop(conclusionId + 1)
        for (unifier <- combinations(unifiers)) {
          // We should try all combinations of unifiers
          val future = (unifyingActor ? Unify(unifier, literals)).mapTo[Option[(Seq[Substitution], Substitution)]]
          futures += future
          future.onSuccess {
            case Some((leftMgu, rightMgu)) =>
              reverseImplicationGraph.synchronized {
                val newLiteral = Literal(rightMgu(conclusion.unit), conclusion.negated)
                val newImplications = unifier.map(_ -> newLiteral)
                if (!unifier.exists(isAncestor(_, newLiteral))) {
                    val newEntry = (clause, unifier zip leftMgu)
                    val newEntriesSet = reverseImplicationGraph(newLiteral) + newEntry
                    reverseImplicationGraph = reverseImplicationGraph + (newLiteral -> newEntriesSet)
                    ancestor(newLiteral) ++= (Set.empty[Clause] /: unifier) (_ union ancestor(_)) + clause
                    mainActor ! Propagated(newLiteral, ancestor(newLiteral).toSeq, reverseImplicationGraph)
                }
              }
            case _ =>
          }
        }
      }
      Await.ready(Future.sequence(futures), Duration.Inf)
      sender ! Resolved()
    case Decision(newLiteral) =>
      decisions += newLiteral
    case PropagationActorUpdate(newClauses, newUnifiableUnits) =>
      allClauses = newClauses
      allClauses.filter(_.isUnit).map(_.literal).foreach(l => ancestor(l) = mutable.Set(l.toClause))
      unifiableUnits = newUnifiableUnits
    case Reset(newClauses) =>
      unifiableUnits = Map.empty[Literal, Set[Literal]].withDefaultValue(Set.empty)
      reverseImplicationGraph =
        Map.empty[Literal, Set[(Clause, Seq[(Literal, Substitution)])]].withDefaultValue(Set.empty)
      decisions.clear()
      allClauses = newClauses
      ancestor.clear()
    case other =>
      log.warning(s"Didn't expect, but got $other")
  }
}
