package at.logic.skeptik.experiment.compression

import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.compressor.guard._
import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.util.time._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import collection.mutable.{ HashSet => MSet }

// Results

class Result (val proof: Proof[SequentProofNode], val time: Double, val count: Int) {

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


//<<<<<<< HEAD
//// WrappedAlgorithm can be neither covariant nor contravariant on P (see experiment function)
//abstract class AbstractWrappedAlgorithm[P](val name: String, val algorithm: ((P) => P) with Duration)
//extends WrappedAlgorithm(name)
//{
//  // P is in contravariant position for p and in covariant position for eval
//  def experiment(p: P, eval: P => Report): Unit = {
//    System.gc()
//    val outProofNode = algorithm(p)
//    val curEval = eval(outProofNode) + ("duration.s" -> algorithm.duration.toDouble / 1000.0)
//    println(name + ": " + curEval)
//    report = report add curEval
//=======
object Result {
  def apply(f: => Proof[SequentProofNode]) = {
    val beginning = System.nanoTime
    val proof = f
    new Result(proof, (System.nanoTime - beginning).toDouble / 1000000.0, 1)
//>>>>>>> 5c9430904afeeb751fcc6f4b516f7e53fe7968c5
  }
}



//<<<<<<< HEAD
//// Ugly hack proving this architecture is wrong
//trait Repeating[P] extends AbstractWrappedAlgorithm[P] {
//  override def experiment(p: P, eval: P => Report): Unit = {
//    System.gc()
//    def rec(duration:Long, run:Int, ratio:Double, proof:P):Unit = {
//      val newProofNode = algorithm(proof)
//      val newDuration = duration + algorithm.duration
//      val curEval = eval(newProofNode) + ("duration.s" -> newDuration.toDouble / 1000.0) + ("run" -> run.toDouble)
//      if (curEval("ratio.%") < ratio) rec(newDuration, run+1, curEval("ratio.%"), newProofNode)
//      else {
//        println(name + ": " + curEval)
//        report = report add curEval
//      }
//    }
//    rec(0, 1, 100.0, p)
//=======
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
//>>>>>>> 5c9430904afeeb751fcc6f4b516f7e53fe7968c5
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
