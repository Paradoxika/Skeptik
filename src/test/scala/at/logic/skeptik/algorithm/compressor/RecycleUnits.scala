package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.parser._
import at.logic.skeptik.proof.measure
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.skeptik.expression.Var

@RunWith(classOf[JUnitRunner])
class RecycleUnitsSpecification extends SpecificationWithJUnit {
  
//  object RecycleUnitsTest {
//  def main(args: Array[String]):Unit = {

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
    val a1 = new Var("1",i)
    val a2 = new Var("2",i)
    val a3 = new Var("3",i)
    val a4 = new Var("4",i)
    val a5 = new Var("5",i)

    val sq1 = new Sequent(Seq(a1,a3),Seq())
    val sq2 = new Sequent(Seq(a2,a5),Seq(a1))
    val sq4 = new Sequent(Seq(a1),Seq(a2))
    val sq5 = new Sequent(Seq(a4),Seq(a1))
    val sq6 = new Sequent(Seq(),Seq(a1,a4))
    
    val c1 = new Axiom(sq1)
    val c2 = new Axiom(sq2)
    val c4 = new Axiom(sq4)
    val c5 = new Axiom(sq5)
    val c6 = new Axiom(sq6)    
    
    val c3 = R.apply(c1,c2)
    val c7 = R.apply(c3,c4)
    val c8 = R.apply(c5,c6)
    concseq = R.apply(c7,c8)
  }
  else {
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
//  val proof = Proof(concseq)
  val proof = ProofParserVeriT.read("F:/Proofs/small-size/iso_icl381.smt2")
    def printProof(proof: Proof[SequentProofNode]) = {
    
    var counter = 0; var result = "";
    proof foldDown { (n:SequentProofNode, r:Seq[Int]) =>
      counter += 1
      result += counter.toString + ": {" + n.conclusion + "} \t: " +
                n.name + "(" + r.mkString(", ") + ")[" + n.parameters.mkString(", ") + "]" + " ~ " + n.hashCode()
      result += "\n"
      counter
    }
    result
  }


  val compproof = RecycleUnits.apply(proof)

  "RecycleUnits" should {
    "compress the proof" in {
      proof.size must beGreaterThan(compproof.size)
    }
  }
}