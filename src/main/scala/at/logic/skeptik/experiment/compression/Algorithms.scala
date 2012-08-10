package at.logic.skeptik.experiment.compression

import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.compressor.guard._
import at.logic.skeptik.proof.sequent.SequentProof
import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.util.time._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import collection.mutable.{ HashSet => MSet }

// Results

class Result (val proof: ProofNodeCollection[SequentProof], val time: Double, val count: Int) {

  // Many measures can be done in the same traversal. We store them.
  lazy val (nbAxioms, nbVariables, axiomsSize) = {
    var nbAxioms = 0
    val variableSet = MSet[E]()
    var axiomsSize = 0
    for (node <- proof) node match {
      case Axiom(clause) =>
        nbAxioms += 1
        variableSet ++= clause.ant.toSet ++ clause.suc.toSet
        axiomsSize += clause.ant.length + clause.suc.length
      case _ =>
    }
    (nbAxioms, variableSet.size, axiomsSize)
  }

}


object Result {
  def apply(f: => ProofNodeCollection[SequentProof]) = {
    val beginning = System.nanoTime
    val proof = f
    new Result(proof, (System.nanoTime - beginning).toDouble / 1000000., 1)
  }
}



// Algorithms

abstract class WrappedAlgorithm (val name: String)
extends Function1[Result,Result] {
  val algo: CompressorAlgorithm[SequentProof]

  protected abstract class InnerGuard
  extends Guard[SequentProof] {
    var beginning:Long = 0
    var duration:Double = 0.
    var count:Int = 0
    def decide(p: ProofNodeCollection[SequentProof]):Boolean
    def apply(p: ProofNodeCollection[SequentProof]) = {
      duration = (System.nanoTime - beginning).toDouble / 1000000.
      count += 1
      decide(p)
    }
    def proceed(original: Result) = {
      beginning = System.nanoTime
      val compressed = algo(original.proof, this)
      new Result(compressed, duration, count)
    }
  }

}   

class TimeOutAlgorithm (name: String, val algo: CompressorAlgorithm[SequentProof])
extends WrappedAlgorithm(name) {
  lazy val factor = environment.getOrElse("timeout","1.").toDouble

  def apply(result: Result) = {
    val guard = new InnerGuard {
      def decide(p: ProofNodeCollection[SequentProof]) = duration < result.time * factor
    }
    guard.proceed(result)
  }

}
