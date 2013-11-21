package at.logic.skeptik.parser

import at.logic.skeptik.parser.ProofParserTraceCheck

object TraceCheckTest {
  def main(args: Array[String]):Unit = {
    val proof = ProofParserTraceCheck.read("examples/proofs/TraceCheck/trace1.tc")
    println(proof)
  }
}