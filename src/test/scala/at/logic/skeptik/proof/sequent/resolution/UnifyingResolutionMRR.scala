package at.logic.skeptik.proof.sequent
package resolution

import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import collection.mutable.Set

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class UnifyingResolutionMRRSpecification extends SpecificationWithJUnit {

  var usedVars = Set[Var]()
  val x = new Var("X", i)
  val y = new Var("Y", i)
  val u = new Var("U", i)
  val z = new Var("Z", i)
  val a = new Var("a", i)
  usedVars += x
  usedVars += u
  usedVars += z
  usedVars += y

  //p(X) |- q(a)     with    q(X) p(Y) |- 
  val leftSeq = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a))
  val rightSeq = Sequent(App(Var("q", i -> i), x))()
  val rightSeqA = App(Var("p", i -> i), y) +: rightSeq
  val leftNode = new Axiom(leftSeq)
  val rightNode = new Axiom(rightSeqA)

  val ur = UnifyingResolutionMRR(leftNode, rightNode)(usedVars)

  //p(b) |- q(a)     with    q(X) p(a) |-
  val b = new Var("b", i)
  val leftSeqB = Sequent(App(Var("p", i -> i), b))(App(Var("q", i -> i), a))
  val rightSeqB = Sequent(App(Var("q", i -> i), x))()
  val rightSeqB2 = App(Var("p", i -> i), a) +: rightSeqB
  val leftNodeB = new Axiom(leftSeqB)
  val rightNodeB = new Axiom(rightSeqB2)

  val urB = UnifyingResolutionMRR(leftNodeB, rightNodeB)(usedVars)

  //p(X) |- q(a) r(Z)     with    q(X) p(a) |- r(U)
  // -> p(a) |- r(Z) r(U)
  val leftSeqC = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a)) + App(Var("r", i -> i), z)
  val rightSeqC = Sequent(App(Var("q", i -> i), x))(App(Var("r", i -> i), u))
  val rightSeqC2 = App(Var("p", i -> i), a) +: rightSeqC
  val leftNodeC = new Axiom(leftSeqC)
  val rightNodeC = new Axiom(rightSeqC2)

  val desiredC = Sequent(App(Var("p", i -> i), a))(App(Var("r", i -> i), z)) + App(Var("r", i -> i), u)
  val urC = UnifyingResolutionMRR(leftNodeC, rightNodeC, desiredC)(usedVars)

  //p(X) |- q(a) r(Z)     with    q(X) p(a) |- r(U)
  // -> p(a) |- r(Z)
  val leftSeqD = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a)) + App(Var("r", i -> i), z)
  val rightSeqD = Sequent(App(Var("q", i -> i), x))(App(Var("r", i -> i), u))
  val rightSeqD2 = App(Var("p", i -> i), a) +: rightSeqD
  val leftNodeD = new Axiom(leftSeqD)
  val rightNodeD = new Axiom(rightSeqD2)

  val desiredD = Sequent(App(Var("p", i -> i), a))(App(Var("r", i -> i), z))
  val urD = UnifyingResolutionMRR(leftNodeD, rightNodeD, desiredD)(usedVars)

  //Test 3-way MRR
  val desiredE = Sequent()()
  val leftSeqE = Sequent(App(Var("q", i -> i), a))()
  val leftSeqEB = App(Var("q", i -> i), y) +: leftSeqE

  val rightSeqE = Sequent()(App(Var("q", i -> i), x))
  val leftNodeEB = new Axiom(leftSeqEB)

  val rightNodeE = new Axiom(rightSeqE)

  val urE = UnifyingResolutionMRR(leftNodeEB, leftNodeEB, rightNodeE, desiredE)(usedVars)

  "UnifyingResolution" should {
    "return the correct resolvent when necessary to make a substitution and a contraction" in {
      Sequent(App(Var("p", i -> i), y))() must beEqualTo(ur.conclusion)
    }
    "return the correct resolvent when unable to make a contraction" in {
      App(Var("p", i -> i), a) +: Sequent(App(Var("p", i -> i), b))() must beEqualTo(urB.conclusion)
    }
    "return the correct resolvent when necessary to make a substitution and a contraction, but not all contractions" in {
      desiredC must beEqualTo(urC.conclusion)
    }
    "return the correct resolvent when necessary to make a substitution and multiple contractions" in {
      desiredD must beEqualTo(urD.conclusion)
    }
    "return the correct resolvent in 3-way MRR" in {
      desiredE must beEqualTo(urE.conclusion)
    }

  }
}