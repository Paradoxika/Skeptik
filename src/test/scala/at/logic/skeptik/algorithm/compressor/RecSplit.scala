package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.algorithm.compressor.split._
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.proof.measure
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}

object RecSplit {
  def main(args: Array[String]):Unit = {
    val testcase = 1
    val a = new Var("a",at.logic.skeptik.expression.i)
    val b = new Var("b",at.logic.skeptik.expression.i)
    val c = new Var("c",at.logic.skeptik.expression.i)
    val d = new Var("d",at.logic.skeptik.expression.i)
    val e = new Var("e",at.logic.skeptik.expression.i)
    val f = new Var("f",at.logic.skeptik.expression.i)
    val g = new Var("g",at.logic.skeptik.expression.i)
    val h = new Var("h",at.logic.skeptik.expression.i)
    val i = new Var("i",at.logic.skeptik.expression.i)
    val j = new Var("j",at.logic.skeptik.expression.i)
    var concseq:SequentProofNode = null
    if (testcase == 0) {
      val n1 = new Axiom(new Sequent(Seq(),Seq(a,c)))
      val n2 = new Axiom(new Sequent(Seq(a),Seq(d,e)))
      val n3 = new Axiom(new Sequent(Seq(e),Seq()))
      val n4 = R(n2,n3) // a |- d
      val n5 = R(n1,n4) // |- cd
      val n6 = new Axiom(new Sequent(Seq(d),Seq(a)))
      val n7 = R(n5,n6) // |- ac
      val n8 = new Axiom(new Sequent(Seq(a),Seq()))
      val n9 = R(n7,n8) // |- c
      val n10 = new Axiom(new Sequent(Seq(c),Seq(d)))
      val n11 = R(n9,n10) // |- d
      val n12 = new Axiom(new Sequent(Seq(d),Seq(c)))
      val n13 = new Axiom(new Sequent(Seq(),Seq(d,b,e)))
      val n14 = R(n3,n13) // |- bd
      val n15 = new Axiom(new Sequent(Seq(c,d),Seq()))
      val n16 = R(n14,n15) // c |- b
      val n17 = R(n12,n16) //d |- b
      val n18 = new Axiom(new Sequent(Seq(d),Seq(c)))
      val n19 = new Axiom(new Sequent(Seq(b),Seq(d)))
      val n20 = R(n18,n19) // b |- c
      val n21 = R(n15,n20) // db |-
      val n22 = R(n17,n21) // d |-
      concseq = R(n11,n22)
    }
    else {
//      val e1 = new Axiom(new Sequent(Seq(j,a),Seq()))
//      val e2 = new Axiom(new Sequent(Seq(),Seq(a)))
      val n1 = new Axiom(new Sequent(Seq(),Seq(c,j)))
      val n2 = new Axiom(new Sequent(Seq(j),Seq()))
//      val n2 = R(e1,e2)
      val n3 = R(n1,n2) // |- c
      val n4 = new Axiom(new Sequent(Seq(c),Seq(i)))
      val n5 = R(n3,n4) // |- i
      val n6 = new Axiom(new Sequent(Seq(i),Seq(c)))
      val n7 = R(n5,n6) // |- c
      val n8 = new Axiom(new Sequent(Seq(c),Seq(a)))
      val n9 = R(n7,n8) // |- a
      val n10 = new Axiom(new Sequent(Seq(a),Seq(f)))
      val n11 = R(n9,n10) // |- f
      val n12 = new Axiom(new Sequent(Seq(f),Seq(a)))
      val n13 = R(n11,n12) // |- a
      val n14 = new Axiom(new Sequent(Seq(a),Seq(e)))
      val n15 = R(n13,n14) // |- e
      val n16 = new Axiom(new Sequent(Seq(e),Seq(a)))
      val n17 = R(n15,n16) // |- a
      val n18 = new Axiom(new Sequent(Seq(a),Seq(d)))
      val n19 = R(n17,n18) // |- d
      val n20 = new Axiom(new Sequent(Seq(d),Seq(a)))
      val n21 = R(n19,n20) // |- a
      val n22 = new Axiom(new Sequent(Seq(),Seq(j,b)))
      val n23 = R(n2,n22) // |- b
      val n24 = new Axiom(new Sequent(Seq(b),Seq(h)))
      val n25 = R(n23,n24) // |- h
      val n26 = new Axiom(new Sequent(Seq(h),Seq(b)))
      val n27 = R(n25,n26) // |- b
      val n28 = new Axiom(new Sequent(Seq(b),Seq(g)))
      val n29 = R(n27,n28) // |- g
      val n30 = new Axiom(new Sequent(Seq(g),Seq(b)))
      val n31 = R(n29,n30) // |- b
      val n32 = new Axiom(new Sequent(Seq(a,b),Seq()))
      val n33 = R(n31,n32)
//      val n2 = R(e1,n21)
      concseq = R(n21,n33)
    }
//    val proof = new Proof(concseq)
//    val proof = ProofParserVeriT.read("F:/Proofs/small-size/gensys_icl052.smt2")
//    val proof = ProofParserVeriT.read("C:/Proofs/very-small/xs-05-19-1-4-2-1.smt2")
    val proof = ProofParserVeriT.read("F:/Proofs/small-size/iso_brn052.smt2")
    val bdS = new DeterministicBoudouSplit(30000)
    val wdS = new DeterministicWDSplit(5000)
    val prS = new DeterministicPRSplit(30000)
    val ssS = new DeterministicSSSplit(5000)
    val adMS = new TimeoutMultiSplit(3,5000)
//    val wdMS = (new WDMultiSplit(2,5000))(proof)
    val prMS = new PRMultiSplit(3,5000)
//    val ssMS = (new SSMultiSplit(2,5000))(proof)
    val adMSp = adMS(proof)
    val prMSp = prMS(proof)
    println("original: " + measure(proof))
    println("adMS: " + measure(adMSp))
//    println("wdMS: " + measure(wdMS))
    println("prMS: " + measure(prMSp))
//    println("ssMS: " + measure(ssMS))
//    val bdsProof = bdS(proof)
//    val wdsProof = wdS.applyOnce(wdS.applyOnce(wdS.applyOnce(proof)))
//    val prsProof = prS(proof)
//    val sssProof = ssS.applyOnce(ssS.applyOnce(ssS.applyOnce(proof)))
//    println("original: " + measure(proof))
//    println("bdS: " + measure(bdsProof))
//    println("wdS: " + measure(wdsProof))
//    println("prS: " + measure(prsProof))
//    println("ssS: " + measure(sssProof))
//    println(proof)
//    val split = new DeterministicBoudouSplit(10)
//    println(split.selectVariable(proof))
//    val splitOnce = split.applyOnce(proof)
//    println(splitOnce)
//    println(split.selectVariable(splitOnce))
//    splitOnce.root.premises.foreach(pr => println(split.selectVariable(pr)))
//    val pr1 = splitOnce.root.premises.head
//    val pr2 = splitOnce.root.premises.last
//    val newProof:SequentProofNode = R(split(pr1).root,split(pr2).root)
//    println(Proof(newProof))

  }
}