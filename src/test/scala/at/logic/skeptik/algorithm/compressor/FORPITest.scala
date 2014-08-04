package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS


object FORPITest {
  def main(args: Array[String]):Unit = {
    
    val proof = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1.spass")
    println(proof)
    val result = FORecyclePivotsWithIntersection(proof)
    println(result)
    
    //Bruno's
    val proofb = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1b.spass")
    println(proofb)
    val resultb = FORecyclePivots(proofb)
    println(resultb)    
     
  }
}