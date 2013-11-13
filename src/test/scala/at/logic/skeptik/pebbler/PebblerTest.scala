package at.logic.skeptik.pebbler

import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.algorithm.compressor.pebbler._
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.proof.measure
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}

object PebblerTest {
  def main(args: Array[String]):Unit = {
    val testcase = 0
    val a = new Var("a",i)
    val b = new Var("b",i)
    val c = new Var("c",i)
    val d = new Var("d",i)
    val e = new Var("e",i)
    val f = new Var("f",i)
    val g = new Var("g",i)
    var concseq:SequentProofNode = null
    if (testcase == 0) {
      val n1 = new Axiom(new Sequent(Seq(),Seq(a,b)))
      val n2 = new Axiom(new Sequent(Seq(),Seq(c,a)))
      val n3 = new Axiom(new Sequent(Seq(c),Seq(a)))
      val n4 = R(n2,n3) // |- a
      val n5 = new Axiom(new Sequent(Seq(b,a),Seq(c)))
      val n6 = new Axiom(new Sequent(Seq(c),Seq(d)))
      val n7 = new Axiom(new Sequent(Seq(a,d),Seq()))
      val n8 = R(n1,n7) // d |- b
      val n9 = new Axiom(new Sequent(Seq(c,b),Seq()))
      val n10 = R(n8,n9) // dc |-
      val n11 = R(n6,n10) // c |-
      val n12 = R(n5,n11) // ba |-
      val n13 = R(n4,n12) // b |-
      concseq = R(n1,n13)
    }
    else {
      val n1 = new Axiom(new Sequent(Seq(),Seq(a,b,c)))
      val n2 = new Axiom(new Sequent(Seq(c),Seq()))
      val n3 = R(n1,n2) // |- ab
      val n4 = new Axiom(new Sequent(Seq(a),Seq()))
      val n5 = R(n1,n4) // |- bc
      val n6 = new Axiom(new Sequent(Seq(b),Seq()))
      val n7 = R(n5,n6) // |- c
      val n8 = new Axiom(new Sequent(Seq(a,c),Seq()))
//      println(n7)
//      println(n8)
      val n9 = R(n7,n8) // a |-
      val n10 = R(n3,n9) // |- b
      val n11 = new Axiom(new Sequent(Seq(b),Seq(c)))
      val n12 = R(n10,n11) // |- c
      val n13 = R(n3,n8) // c |- b
      val n14 = R(n12,n13) // |- b
      val n15 = R(n1,n6) // |- ac
      val n16 = new Axiom(new Sequent(Seq(b,c),Seq()))
      val n17 = R(n15,n16) // b |- a
      val n18 = R(n4,n17) // b |-
      concseq = R(n14,n18)
    }
//    val proof = new Proof(concseq)
//    val proof = ProofParserVeriT.read("F:/Proofs/very-small/hash_uns_04_10.smt2")
    val proof = ProofParserVeriT.read("F:/Proofs/small-size/iso_icl494.smt2")
//    val proof = ProofParserVeriT.read("F:/Proofs/small-size/gensys_icl052.smt2")
//    val proof = ProofParserVeriT.read("examples/proofs/VeriT/eq_diamond2.smt2")
    
    def printBottomUp(node: SequentProofNode, c: Seq[SequentProofNode]):SequentProofNode = {
      println(node + " " + c.size)
      node
    }
    
//    proof bottomUp printBottomUp
//    println(proof)
//    LastChildOfBUPebbler.climbOnce(proof)
    val greedy = LastChildOfBUPebbler(proof)
//    val greedy2 = DistancePebbler(proof)
//    val greedy3 = new GenericPebbler(List("RemovesPebbles","ChildWithPebbledPremise","Distance","InSub","MakesAvailable"))(proof)
//    val generic1 = new GenericBUPebbler(List("LastChild","Children","ProofSize"))
//    val generic2 = new GenericBUPebbler(List("SubProofPebbled","LastChild","Children","ProofSize"))
//    val greedy4 = generic1(proof)
//    val greedy5 = generic2(proof)
//    val climb = generic2.climbOnce(proof)

    val chDC = new ChildrenDecayPebbler(0.5, 2, (A: Seq[Double]) => A.min)
    val lcDC = new LastChildOfDecayPebbler(2, 7, (A: Seq[Double]) => A.max)
    val disDC = new LcoDCthenDistancePebbler(2, 7, (A: Seq[Double]) => A.max)
    
//    println(greedy)
//    println(greedy2)
    
    println("bU: " + measure(greedy)("space"))
//    println("bU2: " + measure(greedy4)("space"))
//    println("bU3: " + measure(greedy5)("space"))
    println("chDC: " + measure(chDC(proof))("space"))
    println("lcDC: " + measure(lcDC(proof))("space"))
    println("disDC: " + measure(disDC(proof))("space"))
//    println("climb: " + measure(climb)("space"))
//    println("tD: " + measure(greedy3)("space"))
    println("normal:" + measure(proof)("space"))
//    println("\ngreedy2:" + measure(greedy2))
  }
}