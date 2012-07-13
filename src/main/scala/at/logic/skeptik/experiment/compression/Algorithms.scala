package at.logic.skeptik.experiment.compression

import at.logic.skeptik.proof.sequent.SequentProof
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.util.time._

// Results

class Result (t: Timed[SequentProof])
extends Timed[SequentProof](t.result, t.time) {
  lazy val nodeCollection = ProofNodeCollection(this.result)
}

class CountedResult (val count: Int, t: Timed[SequentProof])
extends Result(t) {
  def +(other: Timed[SequentProof]) = new CountedResult(count + 1, Timed(other.result, time + other.time))
}


// Algorithms

abstract class WrappedAlgorithm (val name: String)
extends Function1[Result,Result]

class SimpleAlgorithm (name: String, fct: SequentProof => SequentProof)
extends WrappedAlgorithm(name) {
  def apply(result: Result) = new Result(timed { fct(result.result) })
}

class RepeatAlgorithm (name: String, fct: SequentProof => SequentProof)
extends WrappedAlgorithm(name) {
  def apply(result: Result) = {
    def repeat(preceding: CountedResult):CountedResult = {
      val next = preceding + timed { fct(result.result) }
      if (next.nodeCollection.size < preceding.nodeCollection.size) repeat(next) else next
    }
    repeat(new CountedResult(1, result))
  }
}

class TimeOutAlgorithm (name: String, fct: SequentProof => SequentProof)
extends WrappedAlgorithm(name) {
  lazy val factor = environment.getOrElse("timeout","1.").toDouble
  def apply(result: Result) = {
    var timeout = result.time * factor
    def repeat(preceding: CountedResult):CountedResult = {
      val next = preceding + timed { fct(result.result) }
      if (next.time < timeout) repeat(next) else next
    }
    repeat(new CountedResult(1, result))
  }
}

