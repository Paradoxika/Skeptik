package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.parser.ProofParserSPASS

object FORPITest {
  def main(args: Array[String]): Unit = {

    //Should  change the proof
    val proof = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1.spass")
    println(proof)
    val result = FORecyclePivotsWithIntersection(proof)
    println(result)

    //Bruno's -- should change
    val proofb = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1b.spass")
    println(proofb)
    val resultb = FORecyclePivots(proofb)
    println(resultb)

    //Should not change the proof
    val proofc = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1c.spass")
    println(proofc)
    val resultc = FORecyclePivots(proofc)
    println(resultc)

    //Should change the proof
    val proofd = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1d.spass")
    println(proofd)
    val resultd = FORecyclePivots(proofd)
    println(resultd)

    //Should change the proof
    val proofe = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1e.spass")
    println(proofe)
    val resulte = FORecyclePivots(proofe)
    println(resulte)

    //Should change the proof
    val prooff = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1f.spass")
    println(prooff)
    val resultf = FORecyclePivots(prooff)
    println(resultf)

    //should not change
    val proofg = ProofParserSPASS.read("examples/proofs/SPASS/FORPIexample1g.spass")
    println(proofg)
    val resultg = FORecyclePivots(proofg)
    println(resultg)
  }
}