package at.logic.skeptik.algorithm.compressor.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.compressor.congruence._
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.util.io.Input
import at.logic.skeptik.util.io.FileOutput
import scala.collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.congruence._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap}

object ExplanationTest {
  def main(args: Array[String]): Unit = {
    val multiple = true
    val reader = new Input("F:/Proofs/QF_UF/seq_files")
    val output = new FileOutput("experiments/congruence/explComp/explComp6.csv")
    output.write("original, proofTree, origSize, pTsize \n")
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
    var diff = 0
    var equal = 0
    var bigger = 0
    implicit val eqReferences = MMap[(E,E),EqW]()
    proof.foreach(node => {
      val rightEqs = node.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
      val leftEqs = node.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
      
      if (leftEqs.size > 0) {
        rightEqs.foreach(eq => {
          val con = new ProofTreeCongruence().addAll(leftEqs.toList).addNode(eq.l).addNode(eq.r)
          con.explain(eq.l,eq.r) match {
            case Some(path) => {
              val origExpl = leftEqs.size
              val prodExpl = path.originalEqs.size
              val out = path.toProof(eqReferences) match {
                case Some(prodProof) => {
                  val realProofExpl = prodProof.root.conclusion.ant.size
                  val origProofSize = Proof(node).size
                  val prodProofSize = prodProof.size
                  origExpl + "," + prodExpl + ", " + origProofSize + ", " + prodProofSize + "\n"
                  if (origExpl != prodProof.root.conclusion.ant.size) diff = diff + 1
                  if (origExpl == prodProof.root.conclusion.ant.size) equal = equal + 1
                  if (origExpl < prodProof.root.conclusion.ant.size) bigger = bigger + 1
//                  if (origExpl > prodExpl && origProofSize < prodProofSize && prodProofSize < 20) {
//                    println("original:\n"+ Proof(node) + "\nProduced:\n" + prodProof)
//                  }
                  if (realProofExpl < origExpl && prodProofSize > origProofSize) {
//                    println("original:\n"+ Proof(node) + "\nProduced:\n" + prodProof)
                  }
                }
                case None => origExpl + "," + prodExpl + " , , \n"
              }
//              file.write(out)
  //            println(out)
            }
            case _ =>
          }
        })
      }
    })
    println("diff: " + diff + " equal: " + equal + " bigger: " + bigger)
  }
}