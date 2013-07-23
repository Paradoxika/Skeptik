package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import at.logic.skeptik.expression.Var

@RunWith(classOf[JUnitRunner])
class BackwardSubsumptionSpecification extends SpecificationWithJUnit {
//object BackwardSubsumptionSpecification {
//  def main(args: Array[String]):Unit = {
	val testcase = 0
	
  val a = new Var("a",i)
  val b = new Var("b",i)
  val c = new Var("c",i)
  val d = new Var("d",i)
  val e = new Var("e",i)

	var concseq:SequentProofNode = null
	
	if (testcase == 0) {
    val sq1 = new Sequent(Seq(a,d),Seq())
    val sq2 = new Sequent(Seq(b,c),Seq(d))
    val sq3 = new Sequent(Seq(b,c),Seq(a))
    val sq4 = new Sequent(Seq(),Seq(a,c))
    val sq5 = new Sequent(Seq(),Seq(a,b))
    val sq6 = new Sequent(Seq(a,b),Seq())
    val sq7 = new Sequent(Seq(),Seq(b))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
    val ax7 = new Axiom(sq7)
    
    val r1 = R.apply(ax1, ax2)
    val r2 = R.apply(r1,ax3)
    val r3 = R.apply(r2,ax4)
    val r4 = R.apply(r3,ax5)
    val r5 = R.apply(ax6,ax7)
    concseq = R.apply(r4,r5)
	}
	else if (testcase == 1) {
    val sq1 = new Sequent(Seq(a,b,c),Seq())
    val sq2 = new Sequent(Seq(),Seq(c))
    val sq3 = new Sequent(Seq(),Seq(b))
    val sq4 = new Sequent(Seq(a,b),Seq())
    val sq5 = new Sequent(Seq(e),Seq(b))
    val sq6 = new Sequent(Seq(e),Seq(a))
    val sq7 = new Sequent(Seq(),Seq(a,e))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
    val ax7 = new Axiom(sq7)
    
    val r1 = R.apply(ax1, ax2) //ab
    val r2 = R.apply(r1,ax3) //a
    val r3 = R.apply(ax4,ax5) //ae
    val r4 = R.apply(r3,ax6) //e
    val r5 = R.apply(r4,ax7) //-a
    concseq = R.apply(r2,r5)
	}
	else if (testcase == 2)
	{
	  val sq1 = new Sequent(Seq(a,b,c),Seq())
    val sq2 = new Sequent(Seq(),Seq(c))
    val sq3 = new Sequent(Seq(),Seq(a,b))
    val sq4 = new Sequent(Seq(a),Seq())
    val sq5 = new Sequent(Seq(),Seq(a,b))
    val sq6 = new Sequent(Seq(),Seq(a))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
  
    val r1 = R.apply(ax1, ax2) //ab
    val r2 = R.apply(ax3,ax4) //-b
    val r3 = R.apply(r1,r2) //a
    concseq = R.apply(r3,ax6)
	}
	else {
	  val sq1 = new Sequent(Seq(b,c),Seq(a))
    val sq2 = new Sequent(Seq(),Seq(c))
	  val sq3 = new Sequent(Seq(),Seq(b))
    val sq4 = new Sequent(Seq(a,b),Seq())
    val sq5 = new Sequent(Seq(e),Seq(b))
    val sq6 = new Sequent(Seq(e),Seq(a))
    val sq7 = new Sequent(Seq(a),Seq(e))
    
    val ax1 = new Axiom(sq1)
    val ax2 = new Axiom(sq2)
    val ax3 = new Axiom(sq3)
    val ax4 = new Axiom(sq4)
    val ax5 = new Axiom(sq5)
    val ax6 = new Axiom(sq6)
    val ax7 = new Axiom(sq7)
  
    val r1 = R.apply(ax1, ax2)
    val r2 = R.apply(r1,ax3)
    val r3 = R.apply(ax4,ax5)
    val r4 = R.apply(r3,ax6)
    val r5 = R.apply(r4,ax7)
    concseq = R.apply(r2,r5)
	}
  val proof = Proof(concseq:SequentProofNode)
    
//    def visit(node: SequentProofNode, results: Seq[Unit]):Unit = {
//      println(node.conclusion)
//    }
//    
//    proof foldDown(visit)
//    
//    proof bottomUp(visit)
//  println(proof)
   val compproof = BWSm.apply(concseq)
// println(compproof)
  
  "Backward Subsumption" should {
    "compress the proof" in {
      proof.size must beGreaterThan(compproof.size)
    }
    "conclude the empty clause" in {
      compproof.root.conclusion.isEmpty must beTrue
    }
	}
}