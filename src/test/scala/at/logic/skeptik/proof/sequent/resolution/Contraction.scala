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
class ContractionSpecification extends SpecificationWithJUnit {

  var usedVars = Set[Var]()
  val x = new Var("X", i)
  val y = new Var("Y", i)

  val n = new Var("NEW2", i)
  val e = new Var("eq", i -> (i -> i))
  val f = new Var("f", i -> i)
  val two = new Var("2", i)
  val three = new Var("3", i)
  usedVars += x
  usedVars += y

  //First test case
  //(eq (f X) 2), (eq (f NEW2) 2) ⊢
  val f1A = AppRec(e, List(App(f, x), two))
  val f2A = AppRec(e, List(App(f, n), two))

  val seqF2A = Sequent(f2A)()
  val seqA = f1A +: seqF2A

  val premiseA = new Axiom(seqA)

  val conA = Contraction(premiseA)(usedVars)

  //Second test case
  //(eq X 2), (eq (f NEW2) 2) ⊢
  val f1B = AppRec(e, List(x, two))
  val f2B = AppRec(e, List(App(f, n), two))

  val seqF2B = Sequent(f2B)()
  val seqB = f1B +: seqF2B

  //  println("SeqB: " + seqB)
  val premiseB = new Axiom(seqB)

  val conB = Contraction(premiseB)(usedVars)

  //third test case
  //(eq (f X) 2), (eq (f NEW2) 2) ⊢
  val f1C = AppRec(e, List(App(f, x), two))
  val f2C = AppRec(e, List(App(f, n), three))

  //  println("f1: " + f1)
  //  println("f2: " + f2)

  val seqF2C = Sequent(f2C)()
  val seqC = f1C +: seqF2C

  //  println("seqC: " + seqC)

  val premiseC = new Axiom(seqC)

  val conC = Contraction(premiseC)(usedVars)

  //fourth test case
  //given {A(X), A(b) |- B(X)}, the result should be {A(b) |- B(b)}.
  val A = new Var("a", i -> i)
  val B = new Var("b", i -> i)
  val b = new Var("b", i)
  val c = new Var("c", i)

  val seqDtemp = Sequent(App(A, x))(App(B, x))
  val seqD = App(A, b) +: seqDtemp
  val premiseD = new Axiom(seqD)

  val expectedD = Sequent(App(A, b))(App(B, b))

  val conD = Contraction(premiseD)(usedVars)

  //fifth test case
  //multiple contractions: {A(X), A(b), B(Y), B(a) |- }, the result should be {A(b), B(a) |-}.
  val a = new Var("a", i)
  val seqEtemp1 = Sequent(App(A, x))()
  val seqEtemp2 = App(A, b) +: seqEtemp1
  val seqEtemp3 = App(B, y) +: seqEtemp2
  val seqE = App(B, a) +: seqEtemp3
  val premiseE = new Axiom(seqE)
  val conE = Contraction(premiseE)(usedVars)
  val expSeqETemp = Sequent(App(A, b))()
  val expectedE = App(B, a) +: expSeqETemp

  //Sixth test case
  //"|- A(a), A(X), B(X), B(b)"
  val seqFtemp1 = Sequent()(App(A, x))
  val seqFtemp2 = seqFtemp1 + App(A, a)
  val seqFtemp3 = seqFtemp2 + App(B, b)
  val seqFtemp4 = seqFtemp3 + App(B, x)
  val premiseF = new Axiom(seqFtemp4)

  val expSeqFTemp = Sequent()(App(A, a))
  val expectedF = expSeqFTemp + App(A, b) + App(B, b)

  val conF = Contraction(premiseF, expectedF)(usedVars)

  //Seventh test case
  //given: "|- P(a), P(X), Q(X), Q(b)". 
  //desired (wrong) conclusion is "|- P(a), Q(b)"
  val premiseG = premiseF
  val expectedG = Sequent()(App(A, a)) + App(B, b)

  //eighth test case 
  //premise: "|- A(Y), A(X)"
  //desired: "|- A(Y), A(X), A(NEW2)" 
  val seqH = Sequent()(App(A, y)) + App(A, x)
  val premiseH = Axiom(seqH)
  val expectedH = Sequent()(App(A, y)) + App(A, x) + App(A, n)

  //ninth test case 
  //premise: "|- A(Y), A(X), B(a)"
  //desired: "|- A(Y) B(b)"
  //should fail
  val seqI = Sequent()(App(A,y)) + App(A,x) + App(B,c)
  val premiseI = Axiom(seqI)
  val expectedI = Sequent()(App(A,y)) + App(B,b)
  
  //Tenth test case: testing unapply
  val conG =  conA 
  
  //Eleventh: test aux formulae
  //TODO: this one works; convert
  println("conA: " + conA)
  println("auxA: " + conA.auxFormulas)
  
  //12th: aux again
  //TODO: this one fails; convert anyways
  println("conE: " + conE)
  println("auxE: " + conE.auxFormulas)
 
  //13th: test conclusion context
  //TODO: this
  
  "Contraction" should {
    "return the correct resolvent when necessary to make a contract" in {
      Sequent(f2A)() must beEqualTo(conA.conclusion)
    }
    "return the correct resolvent when unifying (f NEW2) with X" in {
      Sequent(f2B)() must beEqualTo(conB.conclusion)
    }
    "return the correct resolvent when no contraction is possible" in {
      seqC must beEqualTo(conC.conclusion)
    }
    "return the correct resolvent necessary to contract to a specific variable" in {
      expectedD must beEqualTo(conD.conclusion)
    }
    "return the correct resolvent necessary to contract multiple terms" in {
      expectedE must beEqualTo(conE.conclusion)
    }

    "return the correct resolvent when the desired one is provided, and a literal in the premise can be unified with many in the desired" in {
      expectedF must beEqualTo(conF.conclusion)
    }

    "fail a requirement when the desired contraction is not valid" in {
      Contraction(premiseG, expectedG)(usedVars) must throwA[IllegalArgumentException]
    }

    "fail a requirement if the desired sequent is longer than the premise" in {
      Contraction(premiseH, expectedH)(usedVars) must throwA[IllegalArgumentException]
    }
    
    "fail a requirement if a literal that has no unifier is not in the desired premise" in {
      Contraction(premiseI, expectedI)(usedVars) must throwA[IllegalArgumentException]
    }
    
    "be matched correctly" in {
      { conG match {
        case Contraction(g, d) => true
        case _ => false
      } } must beEqualTo(true)
    }
  }
}