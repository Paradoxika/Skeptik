package at.logic.skeptik.parser

object LFSCTest {
  def main(args: Array[String]):Unit = {
    val proof = ProofParserLFSC.read("examples/proofs/LFSC/short.lfsc")
    println(proof)
  }
}