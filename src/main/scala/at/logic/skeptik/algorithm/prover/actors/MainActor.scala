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
  @volatile
  var allClauses = cnf.clauses.toSet
  val propagatedLiterals = mutable.Set.empty[Literal]
  @volatile
  var unifiableUnits = Map.empty[Literal, Set[Literal]].withDefaultValue(Set.empty[Literal])
  @volatile
  var decisions = Seq.empty[Literal]
  val literals = mutable.Set.empty[Literal]
  val newClauses = ArrayBuffer.empty[Clause]
  val usedAncestors = mutable.Set.empty[Clause]

  literals ++= allClauses.flatMap(_.literals)

  {
    val unitClauses = allClauses.filter(_.isUnit).map(_.literal)
    unitClauses.foreach(addLiteral)
  }

  @volatile
  var conflictsDeriving = 0
  @volatile
  var clauseResolving = 0

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
