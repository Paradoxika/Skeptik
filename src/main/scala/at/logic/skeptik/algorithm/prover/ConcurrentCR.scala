package at.logic.skeptik.algorithm.prover

import akka.actor.{ActorRef, ActorSystem, Props}
import akka.pattern.ask
import akka.util.Timeout
import at.logic.skeptik.algorithm.prover.actors.{ConflictActor, MainActor, PropagationActor, UnifyingActor}
import at.logic.skeptik.expression.{Var, i}
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.parser.TPTPParsers.{CNFAxiomStatement, CNFNegatedConjectureStatement, CNFProblem, ProblemParserCNFTPTP}

import scala.collection.mutable
import scala.concurrent.{Await, Promise}
import scala.concurrent.duration._

/**
  * @author Daniyar Itegulov
  */
object ConcurrentCR {
  def prove(cnf: CNF)(implicit variables: mutable.Set[Var]): Boolean = {
    implicit val timeout: Timeout = 2 seconds
    implicit val system = ActorSystem()
    val unifyingActor = system.actorOf(Props(new UnifyingActor()), "unify")
    val conflictActor = system.actorOf(Props(new ConflictActor(unifyingActor)), "conflict")
    val propagationActor = system.actorOf(Props(new PropagationActor(unifyingActor)), "propagate")
    val mainActor = system.actorOf(Props(new MainActor(cnf, propagationActor, conflictActor)), "main")

    val future = (mainActor ? "promise").mapTo[Promise[Boolean]]
    val duration = Duration.Inf
    val promise = Await.result(future, duration)
    val result = Await.result(promise.future, duration)
    Await.ready(system.terminate(), Duration.Inf)
    result
  }
}
