package at.logic.skeptik.parser

object SPASSTest {
  def main(args: Array[String]):Unit = {
    val proof = ParserTPTP.read("examples/proofs/SPASS/C(3_3)_attempted_instantiation.tptp")
    println(proof)
  }
}