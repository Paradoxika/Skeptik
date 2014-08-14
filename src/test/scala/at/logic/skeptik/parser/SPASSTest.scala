package at.logic.skeptik.parser

object SPASSTest {
  def main(args: Array[String]):Unit = {

    println("1")
    val proof = ProofParserSPASS.read("examples/proofs/SPASS/completespaceforn_5.spass")
    println(proof.toString)
    
    println("2")
    val proof2 = ProofParserSPASS.read("examples/proofs/SPASS/FSTP2.spass")
    println(proof2)
    
    println("3")
    val proof3 = ProofParserSPASS.read("examples/proofs/SPASS/example2.spass")
    println(proof3)
    
    println("4")
    val proof4 = ProofParserSPASS.read("examples/proofs/SPASS/example1.spass")
    println(proof4)
  }
}