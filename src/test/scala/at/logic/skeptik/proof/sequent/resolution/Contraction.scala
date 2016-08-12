package at.logic.skeptik.proof.sequent
package resolution

import at.logic.skeptik.expression._
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import collection.immutable.Set
import at.logic.skeptik.proof.sequent.resolution._
import collection.mutable.{ HashMap => MMap, Set => MSet }

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class ContractionSpecification extends SpecificationWithJUnit {

  var usedVars = MSet[Var]()
  val x = new Var("X", i)
  val y = new Var("Y", i)
  val u = new Var("U", i)
  val v = new Var("V", i)

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

  val seqF2C = Sequent(f2C)()
  val seqC = f1C +: seqF2C

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
  val seqI = Sequent()(App(A, y)) + App(A, x) + App(B, c)
  val premiseI = Axiom(seqI)
  val expectedI = Sequent()(App(A, y)) + App(B, b)

  //Tenth test case: testing unapply
  val conG = conA

  //Eleventh: test aux formulae
  //uses conA
  val expectedAuxA = "(eq (f X) 2) ⊢ "

  //12th: check main formula
  //uses conE
  val expectedMainA = "(a b), (b a) ⊢"

  //Method level tests
  //conclusion
  //tested in, e.g. object tests with desired

  //mainFormulas
  //see 12th

  //auxFormulas
  //see 11th    

  //contraction
  //newAnt
  //newSuc
  val seqJ = Sequent()(App(A, y)) + App(A, x) + App(B, c)
  val premiseJ = Axiom(seqJ)
  val expectedJ = Sequent()(App(A, x)) + App(B, c)
  val conJ = Contraction(premiseJ, expectedJ)(usedVars)
  val conConJ = conJ.contraction
  val expectedNewAnt = Seq[E]()
  val expectedNewSuc = Seq[E](App(A, x)) ++ Seq[E](App(B, c))
  val expectedCon = (expectedNewAnt, expectedNewSuc, null)

  //checkEmpty
  //instances length == 0; require passes
  val ce1E = App(A, x)
  val ce1ins = Seq[(E, Substitution)]()
  val ce1des = Seq[E](ce1E)

  //instances length == 0; require fails
  val ce2E = App(B, x)
  val ce2ins = Seq[(E, Substitution)]()
  val ce2des = Seq[E](ce1E)

  //instances length != 0
  val ce3E = App(B, x)
  val ce3ins = Seq[(E, Substitution)]((x, Substitution((x, y))))
  val ce3des = Seq[E](ce3E)

  //checkOrContract
  //both empty
  val coc1seqA = Sequent()()
  val coc1seqB = Sequent()()

  //second empty (no desired given)
  val coc2seqA = App(A, y) +: Sequent(App(A, x))()
  val coc2seqB = Sequent()()

  //both non-empty
  val coc3seqA = App(A, y) +: Sequent(App(A, x))()
  val coc3seqB = Sequent(App(A, x))()

  //premise size > 0; pass req
  val coc4seqA = App(A, y) +: Sequent(App(A, x))()
  val coc4seqB = Sequent(App(A, x))()

  //premise size > 0; fail req
  val coc5seqA = App(A, y) +: Sequent(App(A, x))()
  val coc5seqB = App(A, y) +: Sequent(App(A, x))()

  //conclusionContext
  val cc1seqA = App(A, x) +: Sequent(App(A, x))()

  //contract
  //no unifiable pairs
  val con1seqA = App(A, y) +: Sequent(App(B, x))()

  //some unifiable pairs
  val con2seqA = App(A, y) +: App(A, x) +: App(B, y) +: Sequent(App(B, x))()

  //getMaps
  //both empty
  val gm1seqA = Seq[E]()
  val gm1seqB = Seq[E]()

  //identical
  val gm2seqA = Seq[E](App(B, x))
  val gm2seqB = Seq[E](App(B, x))

  //unifiable
  val gm3seqA = Seq[E](App(B, y))
  val gm3seqB = Seq[E](App(B, x))

  //no match
  val gm4seqA = Seq[E](App(A, y))
  val gm4seqB = Seq[E](App(B, x))

  //desiredIsSafe
  //both empty
  val ds1seqA = Sequent()()
  val ds1seqB = Sequent()()

  //not safe
  val ds2seqA = Sequent(App(A, x))()
  val ds2seqB = Sequent()(App(A, x))

  //safe
  val ds3seqA = Sequent(App(A, x))()
  val ds3seqB = Sequent(App(A, x))()

  //buildMap
  //empty outer list
  val bm1 = Seq[Seq[Substitution]]()
  val bm1out = conJ.buildMap(bm1, Sequent()())
  val bm1exp = MMap[Var, Set[E]]()

  //empty inner list
  val bm2 = Seq[Seq[Substitution]](Seq[Substitution]())
  val bm2out = conJ.buildMap(bm2, Sequent()())
  val bm2exp = MMap[Var, Set[E]]()

  //makeSubMap
  //no subs
  val s1 = Seq[Substitution]()
  val s1out = conJ.makeSubMap(s1)
  val s1Expected = MMap[Var, Set[E]]()

  //two different source subs
  val s2 = Seq[Substitution](Substitution((x, y))) ++ Seq[Substitution](Substitution((u, v)))
  val s2out = conJ.makeSubMap(s2)
  val s2Expected = MMap[Var, Set[E]]((x, Set[E](y))) ++ MMap[Var, Set[E]]((u, Set[E](v)))

  //two same source subs
  val s3 = Seq[Substitution](Substitution((x, y))) ++ Seq[Substitution](Substitution((x, v)))
  val s3out = conJ.makeSubMap(s3)
  val s3Expected = MMap[Var, Set[E]]((x, Set[E](y) ++ Set[E](v)))

  //one sub has many
  val s4 = Seq[Substitution](Substitution((x, y), (u, v)))
  val s4out = conJ.makeSubMap(s4)
  val s4Expected = MMap[Var, Set[E]]((x, Set[E](y))) ++ MMap[Var, Set[E]]((u, Set[E](v)))

  //mergeMaps
  //one empty, one full
  val emptyMap = MMap[Var, Set[E]]()
  val nonemptyMap = MMap[Var, Set[E]]((x, Set[E](App(A, x))))
  val mixedInput = Seq[MMap[Var, Set[E]]](emptyMap) ++ Seq[MMap[Var, Set[E]]](nonemptyMap)
  val mixedExpected = nonemptyMap
  val mixedInputOut = conJ.mergeMaps(mixedInput,Sequent()())

  //three maps (all the same)
  val mixedInput3 = Seq[MMap[Var, Set[E]]](nonemptyMap) ++ Seq[MMap[Var, Set[E]]](nonemptyMap) ++ Seq[MMap[Var, Set[E]]](nonemptyMap)
  val mixed3Expected = nonemptyMap
  val mixedInput3Out = conJ.mergeMaps(mixedInput3,Sequent()())

  //three maps (one different)
  val nonemptyMapB = MMap[Var, Set[E]]((y, Set[E](App(B, y))))
  val mixedInput3D = Seq[MMap[Var, Set[E]]](nonemptyMap) ++ Seq[MMap[Var, Set[E]]](nonemptyMapB) ++ Seq[MMap[Var, Set[E]]](nonemptyMap)
  val mixed3DExpected = MMap[Var, Set[E]]((x, Set[E](App(A, x)))) ++ MMap[Var, Set[E]]((y, Set[E](App(B, y))))
  val mixed3DExpectedOut = conJ.mergeMaps(mixedInput3D,Sequent()())

  //three maps (one invalid)
  val nonemptyMapC = MMap[Var, Set[E]]((x, Set[E](App(B, y)))) //invalid
  val mixedInput3E = Seq[MMap[Var, Set[E]]](nonemptyMap) ++ Seq[MMap[Var, Set[E]]](nonemptyMapC) ++ Seq[MMap[Var, Set[E]]](nonemptyMap)

  //both empty
  val manyEmpty = Seq[MMap[Var, Set[E]]](emptyMap) ++ Seq[MMap[Var, Set[E]]](emptyMap) ++ Seq[MMap[Var, Set[E]]](emptyMap)
  val manyEmptyExpected = emptyMap
  val manyEmptyOut = conJ.mergeMaps(manyEmpty, Sequent()())

  //object (apply) tests------

  //no desired - should contract all the way
  val objectTest1seq = Sequent()(App(A, y)) + App(A, x) + App(A, c)
  val objectTest1ax = Axiom(objectTest1seq)
  val objectTest1con = Contraction(objectTest1ax)(usedVars)

  //desired
  val objectTest2seq = Sequent()(App(A, y)) + App(A, x) + App(A, c)
  val objectTest2ax = Axiom(objectTest1seq)
  val objectTest2seqDesired = Sequent()(App(A, y)) + App(A, c)
  val objectTest2con = Contraction(objectTest1ax, objectTest2seqDesired)(usedVars)

  //unapply
  val MconC = Contraction(premiseF, expectedF)(usedVars)
  val MconCresult = MconC match {
    case c: Contraction => true
    case _ => false
  }

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
      {
        conG match {
          case Contraction(g, d) => true
          case _ => false
        }
      } must beEqualTo(true)
    }
    "be matched correctly (2)" in {
      MconCresult must beEqualTo(true)
    }
    "provide the correct aux formulas" in {
      conA.auxFormulas.toString.trim must beEqualTo(expectedAuxA.trim)
    }

    "provide the correct main formulas" in {
      conE.mainFormulas.toString.trim must beEqualTo(expectedMainA.trim)
    }
    "should contract all the way when no desired present" in {
      objectTest1con.conclusion.toString.trim must beEqualTo(" ⊢ (a c)".trim)
    }
    "should contract part way with desired sequent supplied" in {
      objectTest2con.conclusion.toString.trim must beEqualTo("  ⊢ (a Y), (a c)".trim)
    }
    "should return the correct newAnt" in {
      conJ.newAnt must beEqualTo(expectedNewAnt)
    }
    "should return the correct newSuc" in {
      conJ.newSuc must beEqualTo(expectedNewSuc)
    }
    "should return the contraction attribute correctly" in {
      conConJ must beEqualTo(expectedCon)
    }
    
    "should merge empty maps correctly" in {
      manyEmptyOut must beEqualTo(manyEmptyExpected)
    }
    "should merge empty maps correctly" in {
      mixedExpected must beEqualTo(mixedInputOut)
    }
    "should merge 3 of the same maps correctly" in {
      mixedInput3Out must beEqualTo(mixed3Expected)
    }
    "should merge 3 different maps correctly" in {
      mixed3DExpectedOut must beEqualTo(mixed3DExpected)
    }
    "should throw an exception for an invalid map" in {
      conJ.mergeMaps(mixedInput3E, Sequent()()) should throwA[Exception]
    }
    
    "should make subsitution maps correctly (one var replaced with possibly two)" in {
      s3Expected should beEqualTo(s3out)
    }
    "should make subsitution maps correctly (two vars replaced with two vars)" in {
      s2Expected should beEqualTo(s2out)
    }
    "should make subsitution maps correctly (empty list of substitutions)" in {
      s1Expected should beEqualTo(s1out)
    }
    "should make subsitution maps correctly (two vars replaced with two vars; one sub)" in {
      s4Expected should beEqualTo(s4out)
    }
    
    "should build maps given sequences of sequences of substitutions correctly (outer empty)" in {
      bm1exp must beEqualTo(bm1out)
    }
    "should build maps given sequences of sequences of substitutions correctly (inner empty)" in {
      bm2exp must beEqualTo(bm2out)
    }
    
    "check empty - length 0, pass" in {
      conJ.checkEmpty(ce1ins, ce1E, ce1des) must beEqualTo(true)
    }
    "check empty - length 0, fail" in {
      conJ.checkEmpty(ce2ins, ce2E, ce2des) must throwA[Exception]
    }
    "check empty - length != 0, pass" in {
      conJ.checkEmpty(ce3ins, ce3E, ce3des) must beEqualTo(true)
    }
    "check if the supplied desired sequent is safe - both empty" in {
      conJ.desiredIsSafe(ds1seqA, ds1seqB)(usedVars) must beEqualTo((): Unit) //don't care what it returns (in fact, it's not specified)
    }
    "check if the supplied desired sequent is safe - not safe" in {
      conJ.desiredIsSafe(ds2seqA, ds2seqB)(usedVars) must throwA[Exception]
    }
    "check if the supplied desired sequent is safe - safe" in {
      conJ.desiredIsSafe(ds3seqA, ds3seqB)(usedVars) must beEqualTo((): Unit) //don't care what it returns (in fact, it's not specified)
    }
    "check if a desired sequent was supplied -- both empty" in {
      conJ.checkOrContract(coc1seqA, coc1seqB)(usedVars) must beEqualTo((List(), List(), null ))
    }
    "check if a desired sequent was supplied -- second empty (no desired given)" in {
      conJ.checkOrContract(coc2seqA, coc2seqB)(usedVars) must beEqualTo((List(App(A, y)), List(), List(Substitution((x,y)))))
    }
    "check if a desired sequent was supplied -- both non-empty" in {
      conJ.checkOrContract(coc3seqA, coc3seqB)(usedVars) must beEqualTo((List(App(A, x)), List(), null))
    }
    "check if a desired sequent was supplied --premise size > 0; pass req" in {
      conJ.checkOrContract(coc4seqA, coc4seqB)(usedVars) must beEqualTo((List(App(A, x)), List(), null))
    }
    "check if a desired sequent was supplied -- premise size > 0; fail req" in {
      conJ.checkOrContract(coc5seqA, coc5seqB)(usedVars) must throwA[Exception]
    }
    "return the correct conclusion context" in {
      (Contraction(Axiom(cc1seqA))(usedVars)).conclusionContext must beEqualTo(Sequent(App(A, x))())
    }
    "recursively contract correctly - base; nothing to contract" in {
      conJ.contract(con1seqA,null)(usedVars) must beEqualTo((con1seqA.ant, con1seqA.suc, null))
    }
    "recursively contract correctly - things to contract" in {
      conJ.contract(con2seqA, null)(usedVars) must beEqualTo((List(App(A, y), App(B, y)), List(), List(Substitution((x,y)))))
    }
    "get the right substitution maps for a sequent half -- both empty" in {
      conJ.getMaps(gm1seqA, gm1seqB) must beEqualTo(Seq[Seq[Substitution]]())
    }
    "get the right substitution maps for a sequent half -- both identical" in {
      conJ.getMaps(gm2seqA, gm2seqB) must beEqualTo(Seq[Seq[Substitution]]())
    }
    "get the right substitution maps for a sequent half -- both unifiable" in {
      conJ.getMaps(gm3seqA, gm3seqB) must beEqualTo(Seq[Seq[Substitution]](Seq[Substitution](Substitution((x, y)))))
    }
    "get the right substitution maps for a sequent half -- no match" in {
      conJ.getMaps(gm4seqA, gm4seqB) must throwA[Exception]
    }
  }
}