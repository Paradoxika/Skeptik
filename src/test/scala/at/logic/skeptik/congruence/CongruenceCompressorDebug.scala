package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.congruence._
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.proof.measure

object CongruenceCompressorDebug {

  def main(args: Array[String]):Unit = {
  
      val proof = ProofParserVeriT.read("F:/Proofs/QF_UF/QG-classification/qg6/iso_icl_sk004.smt2")
      val newProof = CongruenceCompressor(proof)
      
      println(measure(proof))
      println(measure(newProof))
  }
}