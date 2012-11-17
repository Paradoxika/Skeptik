package at.logic.skeptik.experiment.compression

import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.compressor.guard._
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.util.time._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import collection.mutable.{ HashSet => MSet }
import math.log

// Results

class Result (val proof: Proof[SequentProofNode], val time: Double, val count: Int) {

  // Many measures can be done in the same traversal. We store them.
  lazy val (nbAxioms, nbVariables, axiomsSize, nbLiterals, estimatedVerificationTime) = {
    var nbAxioms = 0
    val variableSet = MSet[E]()
    var axiomsSize = 0
    var nbLiterals = 0
    var estimatedVerificationTime = 0.0
    def clauseSize(clause: Sequent) = clause.ant.length + clause.suc.length
    def log2(x: Double) = log(x) / log(2)
    for (node <- proof) node match {
      case Axiom(clause) =>
        nbAxioms += 1
        variableSet ++= clause.ant.toSet ++ clause.suc.toSet
        val nodeSize = clauseSize(clause)
        axiomsSize += nodeSize
        nbLiterals += nodeSize
      case CutIC(left,right,_,_) =>
        nbLiterals += clauseSize(node.conclusion)
        estimatedVerificationTime += ( (clauseSize(left.conclusion), clauseSize(right.conclusion)) match {
          case (1,m) => log2(m)
          case (m,1) => log2(m)
          case (n,m) if n < m => (n + 1.0) * log2(m + n - 3.0)
          case (m,n) => (n + 1.0) * log2(m + n - 3.0)
        })
      case _ =>
    }
    (nbAxioms, variableSet.size, axiomsSize, nbLiterals, estimatedVerificationTime)
  }

}


object Result {
  def apply(f: => Proof[SequentProofNode]) = {
    val beginning = System.nanoTime
    val proof = f
    new Result(proof, (System.nanoTime - beginning).toDouble / 1000000.0, 1)
  }
}



// Algorithms

abstract class WrappedAlgorithm (val name: String)
extends Function1[Result,Result] {
  val algo: CompressorAlgorithm[SequentProofNode]

  protected abstract class InnerGuard
  extends Guard[SequentProofNode] {
    var beginning:Long = 0
    var duration:Double = 0.0
    var count:Int = 0
    def decide(p: Proof[SequentProofNode]):Boolean
    def apply(p: Proof[SequentProofNode]) = {
      duration = (System.nanoTime - beginning).toDouble / 1000000.0
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

class TimeOutAlgorithm (name: String, val algo: CompressorAlgorithm[SequentProofNode])
extends WrappedAlgorithm(name) {
  def apply(result: Result) = {
    val guard = new InnerGuard {
      def decide(p: Proof[SequentProofNode]) = duration < (result.proof.size + result.axiomsSize).toDouble
    }
    guard.proceed(result)
  }

}
