package at.logic.skeptik.parser

import at.logic.skeptik.parser.ProofParserTraceCheck
import at.logic.skeptik.algorithm.compressor.subsumption._

object TraceCheckTest {
  def main(args: Array[String]):Unit = {
    val proof = ProofParserTraceCheck.read("examples/proofs/TraceCheck/dubois23.trc")
    println(proof)
    println(TopDownSubsumption(proof))
  }
}