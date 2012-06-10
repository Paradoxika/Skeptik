package skeptik.evaluator

import skeptik.proof.oldResolution.{Proof => OldProof, _}
import skeptik.proof._
import skeptik.proof.sequent._
import skeptik.evaluator.generic._


abstract class WrappedAlgorithm (name: String) {
  protected var report : Report = Report.empty
  override def toString() = name + " average: " + report
}


// WrappedAlgorithm can be neither covariant nor contravariant on P (see experiment function)
abstract class AbstractWrappedAlgorithm[P](val name: String, val algorithm: ((P) => P) with Duration)
extends WrappedAlgorithm(name)
{
  // P is in contravariant position for p and in covariant position for eval
  def experiment(p: P, eval: P => Report): Unit = {
    System.gc()
    val outProof = algorithm(p)
    val curEval = eval(outProof) + ("duration.s" -> algorithm.duration.toDouble / 1000.)
    println(name + ": " + curEval)
    report = report add curEval
  }
}

class WrappedOldAlgorithm (name: String, algorithm: ((OldProof) => OldProof) with Duration)
extends AbstractWrappedAlgorithm[OldProof](name, algorithm)
object WrappedOldAlgorithm {
  def apply(name: String, algorithm: ((OldProof) => OldProof)): WrappedOldAlgorithm =
    algorithm match {
      case a:Duration =>
        new WrappedOldAlgorithm(name, a)
      case _ =>
        new WrappedOldAlgorithm(name, DurationMeasuredFunction1(p => algorithm(p.duplicate)))
    }
}
        

class WrappedSequentAlgorithm (name: String, algorithm: ((SequentProof) => SequentProof) with Duration)
extends AbstractWrappedAlgorithm[SequentProof](name, algorithm)
object WrappedSequentAlgorithm {
  def apply(name: String, algorithm: ((SequentProof) => SequentProof)): WrappedSequentAlgorithm =
    algorithm match {
      case a:Duration =>
        new WrappedSequentAlgorithm(name, a)
      case _ =>
        new WrappedSequentAlgorithm(name, DurationMeasuredFunction1(algorithm))
    }
}

// Ugly hack proving this architecture is wrong
trait Repeating[P] extends AbstractWrappedAlgorithm[P] {
  override def experiment(p: P, eval: P => Report): Unit = {
    System.gc()
    def rec(duration:Long, run:Int, ratio:Double, proof:P):Unit = {
      val newProof = algorithm(proof)
      val newDuration = duration + algorithm.duration
      val curEval = eval(newProof) + ("duration.s" -> newDuration.toDouble / 1000.) + ("run" -> run.toDouble)
      if (curEval("ratio.%") < ratio) rec(newDuration, run+1, curEval("ratio.%"), newProof)
      else {
        println(name + ": " + curEval)
        report = report add curEval
      }
    }
    rec(0, 1, 100., p)
  }
}

object RepeatingOldAlgorithm {
  def apply(name: String, algorithm: ((OldProof) => OldProof)): WrappedOldAlgorithm =
    algorithm match {
      case a:Duration =>
        new WrappedOldAlgorithm(name, a) with Repeating[OldProof]
      case _ =>
        new WrappedOldAlgorithm(name, DurationMeasuredFunction1(p => algorithm(p.duplicate))) with Repeating[OldProof]
    }
}

object RepeatingSequentAlgorithm {
  def apply(name: String, algorithm: ((SequentProof) => SequentProof)): WrappedSequentAlgorithm =
    algorithm match {
      case a:Duration =>
        new WrappedSequentAlgorithm(name, a) with Repeating[SequentProof]
      case _ =>
        new WrappedSequentAlgorithm(name, DurationMeasuredFunction1(algorithm)) with Repeating[SequentProof]
    }
}
