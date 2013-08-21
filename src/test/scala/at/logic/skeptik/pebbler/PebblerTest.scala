package at.logic.skeptik.pebbler

import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.Pebbler
import at.logic.skeptik.parser.ProofParserVeriT

object PebblerTest {
  def main(args: Array[String]):Unit = {
    val testcase = 1
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
    val proof = ProofParserVeriT.read("F:/Proofs/small-size/iso_icl739.smt2")
    
    def printBottomUp(node: SequentProofNode, c: Seq[SequentProofNode]):SequentProofNode = {
      println(node + " " + c.size)
      node
    }
    
//    proof bottomUp printBottomUp
//    println(proof)
    val p = new Pebbler[SequentProofNode]
    val greedy = p.greedyPebble(proof)
    val greedy2 = p.greedyPebble2(proof)
//    println(greedy)
//    println(greedy2)
    
    println("\nnormal:" + p.computePebbleNumber(proof))
    println("\ngreedy:" + p.computePebbleNumber(proof,greedy))
    println("\ngreedy2:" + p.computePebbleNumber(proof,greedy2))
  }
}