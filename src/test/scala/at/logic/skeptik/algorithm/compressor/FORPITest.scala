package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS

object FORPITest {
  def main(args: Array[String]): Unit = {

    println("1")
    //Should  change the proof
    val proof = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1.spass")
    println(proof)
    val result = FORecyclePivotsWithIntersection(proof)
    println(result)

    println("2")
    //Bruno's -- should change
    val proofb = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1b.spass")
    println(proofb)
    val resultb = FORecyclePivots(proofb)
    println(resultb)

    println("3")
    //Should not change the proof
    val proofc = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1c.spass")
    println(proofc)
    val resultc = FORecyclePivots(proofc)
    println(resultc)

    println("4")
    //Should change the proof
    val proofd = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1d.spass")
    println(proofd)
    val resultd = FORecyclePivots(proofd)
    println(resultd)

    println("5")
    //Should change the proof
    val proofe = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1e.spass")
    println(proofe)
    val resulte = FORecyclePivots(proofe)
    println(resulte)

    println("6")
    //Should not change the proof
    val prooff = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1f.spass")
    println(prooff)
    val resultf = FORecyclePivots(prooff)
    println(resultf)

    println("7")
    //should not change
    val proofg = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1g.spass")
    println(proofg)
    val resultg = FORecyclePivots(proofg)
    println(resultg)
    
    println("8")
    //Should not change the proof -- MRR test
    val proofh = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1h.spass")
    println(proofh)
    val resulth = FORecyclePivots(proofh)
    println(resulth) 
    
    
    //TODO: add another example that tests intersection where a pivot is shared
    
    //TODO: add another example that tests intersection where a pivot is not shared (but similar)
    
  }
}