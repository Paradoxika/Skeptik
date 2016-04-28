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
class UnifyingResolutionMRRSpecification extends SpecificationWithJUnit with FindDesiredSequent {

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

//  val urE = UnifyingResolutionMRR(leftNodeEB, leftNodeEB, rightNodeE, desiredE)(usedVars)

  //Test aux formula
  val leftSeqF = App(Var("p", i -> i), y) +: Sequent(App(Var("q", i -> i), a))()
  val rightSeqF = Sequent()(App(Var("q", i -> i), x))
  val leftNodeF = new Axiom(leftSeqF)
  val rightNodeF = new Axiom(rightSeqF)
  val urF = UnifyingResolutionMRR(rightNodeF, leftNodeF)(usedVars)
  val urFMRR = urF.asInstanceOf[UnifyingResolutionMRR]
  val computedAuxF = urFMRR.auxL + " " + urFMRR.auxR
  val expectedAuxF = "(q X)" + " " + "(q a)"

  val leftSeqG = Sequent(App(Var("q", i -> i), a))()
  val rightSeqG = Sequent()(App(Var("q", i -> i), x))
  val leftNodeG = new Axiom(leftSeqG)
  val rightNodeG = new Axiom(rightSeqG)
  val urG = UnifyingResolutionMRR(rightNodeG, leftNodeG)(usedVars)
  val urGMRR = urG.asInstanceOf[UnifyingResolutionMRR]
  val computedAuxG = urGMRR.auxL + " " + urGMRR.auxR
  val expectedAuxG = "(q X)" + " " + "(q a)"

  //conclusionContext
  val urH = UnifyingResolutionMRR(rightNodeF, leftNodeF)(usedVars)
  val urHCC = urH.conclusionContext
  val expectedH = Sequent(App(Var("p", i -> i), y))()

  //object (apply) tests
  //2 no desired
  val urI = UnifyingResolutionMRR(rightNodeF, leftNodeF)(usedVars)
  val expectedI = Sequent(App(Var("p", i -> i), y))()

  //2+desired
  val desiredJ = Sequent(App(Var("p", i -> i), x))()
  val urJ = UnifyingResolutionMRR(rightNodeF, leftNodeF, desiredJ)(usedVars)
  val expectedJ = desiredJ
  val resultJ = findRenaming(desiredJ, urJ.conclusion)(usedVars) != null

  //2+bad desired
  val desiredK = Sequent(App(Var("p", i -> i), a))()

  //3 no desired
  val desiredL = Sequent()()
  val leftSeqL = Sequent(App(Var("q", i -> i), a))()
  val leftSeqLB = App(Var("q", i -> i), y) +: leftSeqL

  val rightSeqL = Sequent()(App(Var("q", i -> i), x))
  val leftNodeLB = new Axiom(leftSeqLB)

  val rightNodeL = new Axiom(rightSeqL)

//  val urL = UnifyingResolutionMRR(leftNodeLB, leftNodeLB, rightNodeL)(usedVars)
//  val expectedL = Sequent()()

  //3+desired
  //see above (test 'E')

  //unapply
//  val urM = UnifyingResolutionMRR(leftNodeLB, leftNodeLB, rightNodeL)(usedVars)
//  val outM = urM match {
//    case u: UnifyingResolutionMRR => true
//    case _ => false
//  }

  val urN = UnifyingResolutionMRR(rightNodeF, leftNodeF, desiredJ)(usedVars)
  val outN = urN match {
    case u: UnifyingResolutionMRR => true
    case _ => false
  }

  val urO = UnifyingResolutionMRR(rightNodeF, leftNodeF)(usedVars)
  val outO = urO match {
    case u: UnifyingResolutionMRR => true
    case _ => false
  }

  "UnifyingResolution" should {
    "return the correct resolvent when necessary to make a substitution and a contraction" in {
      Sequent(App(Var("p", i -> i), y))() must beEqualTo(ur.conclusion)
    }
    "return the correct resolvent when unable to make a contraction" in {
      App(Var("p", i -> i), a) +: Sequent(App(Var("p", i -> i), b))() must beEqualTo(urB.conclusion)
    }
    "return the correct resolvent when necessary to make a substitution and a contraction, but not all contractions" in {
       findRenaming(desiredC, urC.conclusion)(usedVars) != null must beEqualTo(true)
    }
    "return the correct resolvent when necessary to make a substitution and multiple contractions" in {
      findRenaming(desiredD,urD.conclusion)(usedVars)!= null  must beEqualTo(true)
    }
//    "return the correct resolvent in 3-way MRR" in {
//      desiredE must beEqualTo(urE.conclusion)
//    }
    "compute the correct aux formulas (with no others present)" in {
      computedAuxF must beEqualTo(expectedAuxF)
    }
    "compute the correct aux formulas (with others present)" in {
      computedAuxG must beEqualTo(expectedAuxG)
    }
    "return the correct conclusion context" in {
      expectedH must beEqualTo(urHCC)
    }
    "resolve two nodes without specifying a desired sequent" in {
      expectedI must beEqualTo(urI.conclusion)
    }
    "resolve two nodes with specifying a desired sequent" in {
      resultJ must beEqualTo(true)
    }
    "throw an exception when the desired sequent is unobtainable" in {
      UnifyingResolutionMRR(rightNodeF, leftNodeF, desiredK)(usedVars) must throwA[Exception]
    }
//    "resolve three nodes to empty correctly" in {
//      urL.conclusion must beEqualTo(expectedL)
//    }
//    "pattern match using unapply correctly (3-way)" in {
//      outM must beEqualTo(true)
//    }
    "pattern match using unapply correctly (2-way; desired)" in {
      outN must beEqualTo(true)
    }
    "pattern match using unapply correctly (2-way)" in {
      outO must beEqualTo(true)
    }
  }
}