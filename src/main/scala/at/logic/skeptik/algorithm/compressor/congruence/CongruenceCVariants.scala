package at.logic.skeptik.algorithm.compressor.congruence

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import at.logic.skeptik.congruence._
import at.logic.skeptik.congruence.structure.EqW
import at.logic.skeptik.expression.E
import at.logic.skeptik.congruence.structure._

trait ArrayCompressor {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    new ArrayCongruence(new FindTable(), Queue[(E,E)](), WEqGraph(eqReferences))
  }
}

trait FibonacciCompressor {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    new FibonacciCongruence(new FindTable(), Queue[(E,E)](), WEqGraph(eqReferences))
  }
}

trait ProofTreeCompressor {
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): Congruence = {
    new ProofTreeCongruence(new FindTable(), Queue[(E,E)](), ProofForest())
  }
}

trait global {
  def globalAxioms = true
}

trait local {
  def globalAxioms = false
}

object ArrayC extends CongruenceCompressor with ArrayCompressor with local

object FibonacciC extends CongruenceCompressor with FibonacciCompressor with local

object ProofTreeC extends CongruenceCompressor with ProofTreeCompressor with local
