package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.algorithm.compressor.split._
import at.logic.skeptik.parser._
import at.logic.skeptik.proof.measure
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}
import at.logic.skeptik.exporter._
import at.logic.skeptik.util.time._

object RecSplitTest {
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
    else if (testcase == 1){
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
    else {
      val n1 = new Axiom(new Sequent(Seq(),Seq(b,d)))
      val n2 = new Axiom(new Sequent(Seq(b),Seq(c)))
      val n3 = R(n1,n2)
      val n4 = new Axiom(new Sequent(Seq(b,c),Seq()))
      val n5 = R(n1,n4)
      val n6 = R(n3,n5)
      val n7 = new Axiom(new Sequent(Seq(a,d),Seq()))
      val n8 = R(n6,n7)
      val n9 = new Axiom(new Sequent(Seq(d),Seq(a)))
      val n10 = R(n6,n9)
      concseq = R(n8,n10)
    }
//    val proof = new Proof(concseq)
//    val proofExporter = ProofExporterVeriT.write(proof, "RecursiveSplit")
//    val proof = ProofParserSkeptik.read("examples/proofs/Skeptik/msplit.skeptik")
    val proof = ProofParserVeriT.read("examples/proofs/VeriT/eq_diamond5.smt2")
//    val proof = ProofParserVeriT.read("C:/Proofs/very-small/xs-05-19-1-4-2-1.smt2")
//    val proof = ProofParserVeriT.read("F:/Proofs/small-size/iso_brn052.smt2")
//    val proof = ProofParserVeriT.read("C:/Proofs/very-small/prp-2-17.smt2")
//    println(proof.foreach(f => println(f.conclusion)))
//    val bdS = new DeterministicBoudouSplit(5)
    val wdS = new WDSplit(5000)
    val priS = new PRISplit(5000)
    val puiS = new PUISplit(5000)
    val ssS = new SSSplit(5000)
    val adMS = new TimeoutMultiSplit(2,5000)
    val prMS = new PRMultiSplit(3,5000)
    val recS = new DetADRecSplitTime(2000,5000)
    val recS2 = new DepthTimeRS(3,5000)
    val RSTDS5000 = new RSTDS(2000,5000)
    val its = new IterativeSplit(3)
    println(measure(proof))
//    println(proof)
    val Timed(cp,time) = timed { measure(its(proof)) }
    println(time + "\n" + cp)
//    val Timed(cp2,time2) = timed { measure(recS2(proof)) }
//    println(time2 + "\n" + cp2)
//    println(bdS.applyOnce(proof))
//    val wdMS = (new WDMultiSplit(2,5000))(proof)
    
//    val ssMS = (new SSMultiSplit(2,5000))(proof)
//    val adMSp = adMS(proof)
//    val prMSp = prMS(proof)
//    println("original: " + measure(proof))
//    println("adMS: " + measure(adMSp))
//    println("wdMS: " + measure(wdMS))
//    println("prMS: " + measure(prMSp))
//    println("ssMS: " + measure(ssMS))
//    val bdsProof = bdS(proof)
//    val wdsProof = wdS.applyOnce(wdS.applyOnce(wdS.applyOnce(proof)))
//    val prisProof = priS(proof)
//    val puisProof = puiS(proof)
//    val sssProof = ssS.applyOnce(ssS.applyOnce(ssS.applyOnce(proof)))
//    println("original: " + measure(proof))
//    println("bdS: " + measure(bdsProof))
//    println("wdS: " + measure(wdsProof))
//    println("priS: " + measure(prisProof))
//    println("puiS: " + measure(puisProof))
//    println("ssS: " + measure(sssProof))
//    println(proof)
//    val split = new DeterministicBoudouSplit(10)
//    println(bdS.selectVariable(proof))
//    val (l,r) = bdS.split(proof,a)
//    val splitOnce = R(l,r,a,true)
//    println(splitOnce)
//    val (ll,lr) = bdS.split(l,c)
//    val (rl,rr) = bdS.split(r,b)
//    println(ll + " ~ " + lr)
//    val nl = R(ll,lr)
//    val nr = R(rl,rr)
//    val newProof:SequentProofNode = R(nl,nr)
//    println(Proof(newProof))
    //    val measures = new RecSplit(2).computeMeasuresSplitVersion(proof)
//    measures.foreach(m => {
//      println("measures for " + m._1 + ":")
//      m._2.foreach(println)
//    })
//    val rS = new RecSplit(2)
//    val Timed(varTree,varTreeTime) = timed { rS.computeVariableTree(proof) }
//    val Timed(varSeq,varSeqTime) = timed { rS.computeVariablesSeq(proof) }
//    val Timed(varTree2,varTree2Time) = timed { rS.computeVarTreeWithSplitting(proof) }
//    println("Tree completed in: " + varTreeTime)
//    println("Seq completed in: " + varSeqTime)
//    println("Tree2 completed in: " + varTree2Time)
//    
//    println(varTree)
//    
//    println(varTree2)
//    
//    println(measure(proof))
  }
}