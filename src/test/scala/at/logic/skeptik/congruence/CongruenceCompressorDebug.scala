package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.congruence._
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.parser.ProofParserSkeptik
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.io.Input

object CongruenceCompressorDebug {

  def main(args: Array[String]):Unit = {
    val multiple = false
    val reader = new Input("F:/Proofs/QF_UF/seq_files")
//    val file = "F:/Proofs/QF_UF/SEQ/SEQ005_size6.smt2"
//    val file = "experiments/congruence/resolveBug.s"
      val file = "experiments/congruence/resolveBug3.smt2"
    val parser = ProofParserVeriT
//    val parser = ProofParserSkeptik
    if (multiple) {
      val lines = reader.lines
  //    var percentage: Double = - 1
      for (singleFile <- lines) {
        println("parsing " + singleFile)
        val proof = parser.read(singleFile)
        println("finished parsing")
  //      val proof = ProofParserVeriT.read("F:/Proofs/QF_UF/SEQ/SEQ032_size2.smt2")
        val newProof = CongruenceCompressor(proof)
        println(measure(proof))
        println(measure(newProof))
        println(newProof.root)
      }
    }
    else {
      val proof = parser.read(file)
      val newProof = CongruenceCompressor(proof)
      println(measure(proof))
      println(measure(newProof))
      println(newProof.root)
    }
  }
}