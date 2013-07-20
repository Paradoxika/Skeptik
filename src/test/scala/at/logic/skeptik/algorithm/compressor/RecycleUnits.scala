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
class RecycleUnitsSpecification extends SpecificationWithJUnit {

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
    val c9 = R.apply(c7,c8)
    
    val proof = Proof(c9:SequentProofNode)
  
    "RecycleUnits" should {
      "compress the proof" in {
        val compproof = RecycleUnits.apply(proof)
        proof.size must beGreaterThan(compproof.size)
      }
	}
}