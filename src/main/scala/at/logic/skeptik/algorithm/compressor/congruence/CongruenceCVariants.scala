package at.logic.skeptik.algorithm.compressor.congruence


import at.logic.skeptik.congruence._

trait global {
  def globalAxioms = true
}

trait local {
  def globalAxioms = false
}

object ArrayC extends CongruenceCompressor with ArrayStructure with local

object FibonacciC extends CongruenceCompressor with FibonacciStructure with local

object ProofTreeC extends CongruenceCompressor with ProofTreeStructure with local


object ArrayCNew extends CongruenceCompressorNew with ArrayStructure

object FibonacciCNew extends CongruenceCompressorNew with FibonacciStructure

object ProofTreeCNew extends CongruenceCompressorNew with ProofTreeStructure

object ArrayCNewNew extends CongruenceCompressorNew with ArrayStructureNew

object FibonacciCNewNew extends CongruenceCompressorNew with FibonacciStructureNew

object ProofTreeCNewNew extends CongruenceCompressorNew with ProofTreeStructureNew


