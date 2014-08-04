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
    
    //Should not change the proof
    val proofc = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1c.spass")
    println(proofc)
    val resultc = FORecyclePivots(proofc)
    println(resultc)   
     
    println("STARTING LAST")
    
    //Should change the proof
    val proofd = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1d.spass")
    println(proofd)
    val resultd = FORecyclePivots(proofd)
    println(resultd)       
  }
}