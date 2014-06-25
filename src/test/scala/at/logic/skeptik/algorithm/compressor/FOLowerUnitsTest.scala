package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS


object FOLowerUnitsTest {
  def main(args: Array[String]):Unit = {
    
    val proof = ProofParserSPASS.read("examples/proofs/SPASS/example2.spass")
    println(proof)
    
    FOLowerUnits(proof)
  }
}