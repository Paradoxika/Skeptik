package at.logic.skeptik.algorithm.prover.actors

import akka.actor.{Actor, ActorLogging, ActorRef}
import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.algorithm.prover.actors.messages._
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.expression.Var
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.SequentProofNode

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import scala.concurrent.Promise
import scala.util.Random

/**
  * @author Daniyar Itegulov
  */
class MainActor(cnf: CNF, propagationActor: ActorRef, conflictActor: ActorRef)
               (implicit variables: mutable.Set[Var]) extends Actor with ActorLogging {
  /*
   * All mutable variables (vars) should be marked with @volatile.
   *
   * See this for more details: http://doc.akka.io/docs/akka/current/general/jmm.html
   */

  // Initial clauses + conflict driven clauses
  @volatile
  var allClauses = cnf.clauses.toSet
  // Literals, propagated at all depths
  val propagatedLiterals = mutable.Set.empty[Literal]
  // For each literal we want to know what literals are unifiable with it
  @volatile
  var unifiableUnits = Map.empty[Literal, Set[Literal]].withDefaultValue(Set.empty[Literal])
  // Decided literals
  @volatile
  var decisions = Seq.empty[Literal]
  // All literals (as a part of initial clause or as a propagated literal)
  val literals = mutable.Set.empty[Literal]
  // Clauses to be added on this level
  val newClauses = ArrayBuffer.empty[Clause]
  // Initial clauses, which already have been used
  val usedAncestors = mutable.Set.empty[Clause]

  literals ++= allClauses.flatMap(_.literals)

  {
    val unitClauses = allClauses.filter(_.isUnit).map(_.literal)
    unitClauses.foreach(addLiteral)
  }

  // Number of conflicts, which are being (at this time) derived by ConflictActor
  @volatile
  var conflictsDeriving = 0
  // Number of clauses, which are being (at this time) resolved by PropagationActor
  @volatile
  var clauseResolving = 0

  // Promise for result of alrogithm
  val promise = Promise[Option[Proof[SequentProofNode]]]()

  def propagate(reverseImpGraph: Map[Literal, Set[(Clause, Seq[(Literal, Substitution)])]]): Unit = {
    for (decisionLiteral <- decisions) {
      // Check for a conflict
      if (unifiableUnits(decisionLiteral).nonEmpty) {
        val otherLiteral = unifiableUnits(decisionLiteral).head
        conflictsDeriving += 1
        conflictActor ! Conflict(decisionLiteral, otherLiteral, allClauses, decisions, reverseImpGraph)
      }
    }
    if (newClauses.nonEmpty) {
      allClauses = allClauses ++ newClauses
      newClauses.clear()
      decisions = Seq.empty[Literal]
      literals.clear()
      literals ++= allClauses.flatMap(_.literals)
      propagatedLiterals.clear()

      unifiableUnits = Map.empty[Literal, Set[Literal]].withDefaultValue(Set.empty[Literal])

      val unitClauses = allClauses.filter(_.isUnit).map(_.literal)
      unitClauses.foreach(addLiteral)

      propagationActor ! Reset(allClauses)
    }
    propagationActor ! PropagationActorUpdate(allClauses, unifiableUnits)
    for (clause <- allClauses if !clause.isUnit) {
      clauseResolving += 1
      propagationActor ! Resolve(clause)
    }
  }

  def addLiteral(newLiteral: Literal): Unit = {
    propagatedLiterals += newLiteral
    literals += newLiteral
    val newEdges =
      for (literal <- literals if newLiteral.negated != literal.negated)
        yield unifyWithRename(Seq(literal.unit), Seq(newLiteral.unit))
          .map(_ => literal -> (unifiableUnits(literal) + newLiteral))
    val newUnifiables = newEdges.flatten.toSeq
    val newSelfEdges = for (literal <- propagatedLiterals if newLiteral.negated != literal.negated)
      yield unifyWithRename(Seq(literal.unit), Seq(newLiteral.unit))
          .map(_ => newLiteral -> Set(literal))
    val newSelfUnifiables = newSelfEdges.flatten.toSeq

    unifiableUnits = unifiableUnits ++ newUnifiables ++ newSelfUnifiables
  }

  propagate(Map.empty)

  override def receive: Receive = {
    case Propagated(newLiteral, ancestors, reverseImpGraph) =>
      log.info(s"Propagated $newLiteral")
      // Update system state
      usedAncestors ++= ancestors

      if (decisions contains newLiteral) {
        decisions = decisions.filterNot(_ == newLiteral)
      }

      addLiteral(newLiteral)

      // Check for a conflict
      if (unifiableUnits(newLiteral).nonEmpty) {
        val otherLiteral = unifiableUnits(newLiteral).head
        conflictsDeriving += 1
        conflictActor ! Conflict(newLiteral, otherLiteral, allClauses, decisions, reverseImpGraph)
      }
    case Derived(newClause, reverseImpGraph, conflict) =>
      conflictsDeriving -= 1
      newClauses += newClause

      if (newClause.isEmpty) {
        promise.trySuccess(Some(Proof(conflict)))
      }

      if (clauseResolving == 0 && conflictsDeriving == 0) {
        propagate(reverseImpGraph)
      }
    case Resolved(reverseImpGraph) =>
      clauseResolving -= 1
      if (clauseResolving == 0) {
        def satisfied = cnf.clauses.filter(_.literals.exists(lit => propagatedLiterals contains lit))
        def notUsedAncestors = Random.shuffle((cnf.clauses.toSet diff (usedAncestors ++ satisfied)).toSeq)
        if (notUsedAncestors.nonEmpty) {
          val clause = notUsedAncestors.head
          val decisionLiteral = Random.shuffle(clause.literals).head
          decisions = decisions :+ decisionLiteral
          usedAncestors += clause
          addLiteral(decisionLiteral)

          log.info(s"Made decision $decisionLiteral")

          propagationActor ! Decision(decisionLiteral)
          for (ancestor <- notUsedAncestors) {
            clauseResolving += 1
            propagationActor ! Resolve(clause)
          }
        }
      }
      if (clauseResolving == 0 && conflictsDeriving == 0) {
        propagate(reverseImpGraph)
      }
    case "promise" =>
      sender ! promise
    case other =>
      log.warning(s"Didn't expect, but got $other")
  }
}
