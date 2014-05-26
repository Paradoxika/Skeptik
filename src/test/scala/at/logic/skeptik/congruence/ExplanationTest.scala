package at.logic.skeptik.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.compressor.congruence._
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.parser.ProofParserSkeptik
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.io.Input
import at.logic.skeptik.util.io.FileOutput
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.congruence._

object ExplanationTest {
  def main(args: Array[String]): Unit = {
    val multiple = true
    val reader = new Input("F:/Proofs/QF_UF/seq_files")
    val output = new FileOutput("experiments/congruence/explComp/explComp3.csv")
    output.write("original, proofTree \n")
    val file = "F:/Proofs/QF_UF/SEQ/SEQ005_size6.smt2"
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
        measureExpls(proof,output)
      }
    }
    else {
      val proof = parser.read(file)
      println("finished parsing")
      val t = System.currentTimeMillis()
      val newProof = FibonacciC(proof)
      val timeReq = System.currentTimeMillis() - t
      measureExpls(proof,output)
    }
  }
  
  def measureExpls(proof: Proof[N], file: FileOutput) = {
    val eqReferences = MMap[(E,E),EqW]()
    proof.foreach(node => {
      val rightEqs = node.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_,eqReferences))
      val leftEqs = node.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_,eqReferences))
      
      rightEqs.foreach(eq => {
        val con = new ProofTreeCongruence(eqReferences).addAll(leftEqs.toList).addNode(eq.l).addNode(eq.r)
        con.explain(eq.l,eq.r) match {
          case Some(path) => {
            val out = leftEqs.size + "," + path.originalEqs.size + " \n"
            file.write(out)
//            println(out)
          }
          case _ =>
        }
      })
    })
  }
}