package at.logic.skeptik.parser

object SPASSTest {
  def main(args: Array[String]):Unit = {
    //val proof = ProofParserSPASS.read("examples/proofs/SPASS/C(3_3)_attempted_instantiation.spass")
    val proof = ProofParserSPASS.read("examples/proofs/SPASS/completespaceforn_5.spass")
    println(proof)
    val proof2 = ProofParserSPASS.read("examples/proofs/SPASS/FSTP2.spass")
    println(proof2)
    
    val proof3 = ProofParserSPASS.read("examples/proofs/SPASS/example2.spass")
    println(proof3)
  }
}