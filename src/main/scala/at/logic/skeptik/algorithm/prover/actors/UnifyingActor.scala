package at.logic.skeptik.algorithm.prover.actors

import akka.actor.{Actor, ActorLogging}
import at.logic.skeptik.algorithm.prover.actors.messages.{GetVariables, Unify}
import at.logic.skeptik.algorithm.prover._
import at.logic.skeptik.expression.Var

import scala.collection.mutable

/**
  * @author Daniyar Itegulov
  */
class UnifyingActor(implicit variables: mutable.Set[Var]) extends Actor with ActorLogging {

  override def receive: Receive = {
    case Unify(left, right) =>
      sender ! unifyWithRename(left.map(_.unit), right.map(_.unit))
    case GetVariables =>
      sender ! variables.toSet
    case other =>
      log.warning(s"Didn't expect, but got $other")
  }
}
