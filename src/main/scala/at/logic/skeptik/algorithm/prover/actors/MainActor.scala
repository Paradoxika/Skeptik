package at.logic.skeptik.algorithm.prover.actors

import akka.actor.{Actor, ActorLogging, ActorRef}
import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.algorithm.prover.actors.messages._
import at.logic.skeptik.algorithm.prover.structure.immutable.Literal
import at.logic.skeptik.expression.Var

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
  var allClauses = cnf.clauses
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

  val promise = Promise[Boolean]()

  def propagate(): Unit = {
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

  propagate()

  override def receive: Receive = {
    case Propagated(newLiteral, ancestors, reverseImpGraph) =>
      log.info(s"Propagated $newLiteral")
      // Update system state
      usedAncestors ++= ancestors
      addLiteral(newLiteral)

      // Check for a conflict
      if (unifiableUnits(newLiteral).nonEmpty) {
        val otherLiteral = unifiableUnits(newLiteral).head
        conflictsDeriving += 1
        conflictActor ! Conflict(newLiteral, otherLiteral, allClauses, decisions, reverseImpGraph)
      }
    case Derived(newClause) =>
      conflictsDeriving -= 1
      newClauses += newClause

      if (newClause.isEmpty) {
        promise.success(false)
      }

      if (clauseResolving == 0 && conflictsDeriving == 0) {
        propagate()
      }
    case Resolved() =>
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
        propagate()
      }
    case "promise" =>
      sender ! promise
    case other =>
      log.warning(s"Didn't expect, but got $other")
  }
}
