package at.logic.skeptik.parser

import at.logic.skeptik.parser.ProofParserLFSC;

object LFSCTest {
  def main(args: Array[String]):Unit = {
    val proof = ProofParserLFSC.read("examples/proofs/LFSC/short.lfsc")
    println(proof)
  }
}