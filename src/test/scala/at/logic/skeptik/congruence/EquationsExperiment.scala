package at.logic.skeptik.congruence

import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.algorithm.congruence
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof._
import at.logic.skeptik.util.io.Input
import at.logic.skeptik.algorithm.congruence._

object EquationsExperiment {

  def main(args: Array[String]):Unit = {
    val reader = new Input("F:/Proofs/QF_UF/QG-classification/QC-classification")
//    val reader = new Input("F:/Proofs/QF_UF/seq_files")
//    val reader = new Input("D:/Paradoxika/Skeptik/prooflists/diamonds")
    val lines = reader.lines
    val parser = ProofParserVeriT
//    var percentage: Double = - 1
    for (singleFile <- lines) {
      val proof = parser.read(singleFile)
      val axioms = proof.filter(n => n.premises.isEmpty)
      val y = countTwoRightAndCongruent(proof)
//      val x = countTrueAxioms(axioms)
//      if (percentage == -1) percentage = x
//      else percentage = (percentage + x)/2
//      println(percentage + " % two right and congruent at: " + singleFile)
//      println(x + " of " + axioms.size + " two right and congruent at: " + singleFile)
      println(y + " of " + proof.size + " two right and congruent at: " + singleFile)
    }
//    println(percentage)
    
  }
  
  def countTrueAxioms(axioms: Iterable[N]) = {
    var count = 0
    axioms.foreach(node => {
      if (toRightAndCongruent(node)) { 
        count = count + 1
      }
    })
    count
  }
  
  def countTwoRightAndCongruent(proof: Proof[N]) = {
    var count = 0
    proof.foreach(node => {
      if (toRightAndCongruent(node)) { 
        count = count + 1
      }
    })
//    (count.asInstanceOf[Double] * 100) / proof.size
    count
  }
  
  def countTwoRight(proof: Proof[N]) = {
    var count = 0
    proof.foreach(node => {
      if (hasTwoRight(node)) {
//        if (node.conclusion.size < 10) println(node.conclusion)
        count = count + 1
      }
    })
//    println(count +" of "+ proof.size + " have 2 eq's right")
//    (count.asInstanceOf[Double] * 100) / proof.size
    count
  }
  
  def toRightAndCongruent(node: N): Boolean = {
    val rightEqs = node.conclusion.suc.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
    val leftEqs = node.conclusion.ant.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
    val s = rightEqs.size
    val twoAndCongruent =
      if (s > 0) {
        val con = new Congruence
        leftEqs.foreach(eq => con.addEquality(eq))
        con.resolveDeduced
        rightEqs.exists(eq => {
          val path = con.explain(eq.function.asInstanceOf[App].argument, eq.argument)
          val c = path.collectLabels.size
          val out = c > 0 && c < leftEqs.size
//          if (out) {
//            println(node.conclusion + "\nshorter explanation " + path.collectLabels)
//          }
//          if (!out) println(node.conclusion)
//          println("is congruent: " + eq.function.asInstanceOf[App].argument + ", " + eq.argument + " ? " + c)
          out
        })
      }
      else false
//      if (s > 0 && leftEqs.size > 0 && !twoAndCongruent) {
//        println(node.conclusion)
//      }
      twoAndCongruent
  }
  
  def hasTwoRight(node: N): Boolean = {
    val s = node.conclusion.suc.filter(Eq.?:(_)).size
//    println(s)
    s > 1
  }
}