package at.logic.skeptik.algorithm.compressor.congruence


import at.logic.skeptik.congruence._

trait global {
  def globalAxioms = true
}

trait local {
  def globalAxioms = false
}

object ArrayCongruence extends CongruenceCompressor with ArrayStructure

object FibonacciCongruence extends CongruenceCompressor with FibonacciStructure

object ProofTreeCongruence extends CongruenceCompressor with ProofTreeStructure


