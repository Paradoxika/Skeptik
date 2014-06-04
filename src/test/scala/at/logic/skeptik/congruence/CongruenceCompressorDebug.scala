package at.logic.skeptik.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.compressor.congruence._
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.parser.ProofParserSkeptik
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.io.Input
import scala.collection.mutable.{HashMap => MMap}

object CongruenceCompressorDebug {

  def main(args: Array[String]):Unit = {
    
    val x = MMap[(Int,Int),Int]()

    x.getOrElse((0,1),x.getOrElseUpdate((1,0), 2))
    
    println(x.getOrElse((0,1),x.getOrElseUpdate((1,0), 6)))
    
    val multiple = true
    val reader = new Input("F:/Proofs/QF_UF/seq_files")
//    val file = "F:/Proofs/QF_UF/SEQ/SEQ005_size6.smt2"
    val file = "F:/Proofs/QF_UF/SEQ/SEQ005_size8.smt2"
//    val file = "F:/Proofs/QF_UF/SEQ/SEQ013_size4.smt2"
//      val file = "F:/Proofs/QF_UF/SEQ/SEQ032_size2.smt2"
//    val file = "F:/Proofs/QF_UF/SEQ/SEQ010_size8.smt2"
//    val file = "F:/Proofs/QF_UF/SEQ/SEQ010_size6.smt2"
//      val file = "F:/Proofs/QF_UF/SEQ/SEQ010_size8.smt2"
//    val file = "F:/Proofs/QF_UF/SEQ/SEQ004_size5.smt2"
//    val file = "experiments/congruence/resolveBug.s"
//      val file = "experiments/congruence/resolveBug10_1.smtb"
    val parser = ProofParserVeriT
//    val parser = ProofParserSkeptik
    if (multiple) {
      val lines = reader.lines
  //    var percentage: Double = - 1
      for (singleFile <- lines) {
        println("parsing " + singleFile)
        val proof = parser.read(singleFile)
        println("finished parsing")
        val newProof = ProofTreeCNewNew(proof)
        println(measure(proof))
        println(measure(newProof))
        println(newProof.root)
      }
    }
    else {
      val proof = parser.read(file)
      println("finished parsing")
//      println(proof)
      val t = System.currentTimeMillis()
      val newProof = ProofTreeCNewNew(proof)
      val timeReq = System.currentTimeMillis() - t
      println("time: " + timeReq + "ms")
      println(measure(proof))
      println(measure(newProof))
      println(newProof.root)
//      println(proof)
    }
  }
}