package at.logic.skeptik.parser

import at.logic.skeptik.parser.ProofParserLFSC;

object SPASSTest {
  def main(args: Array[String]):Unit = {
    val proof = ProofParserSPASS.read("examples/proofs/SPASS/C(3_3)_attempted_instantiation.tptp")
    println(proof)
  }
}