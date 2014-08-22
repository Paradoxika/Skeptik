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
class UnifyingResolutionSpecification extends SpecificationWithJUnit with FindsVars {

  var usedVars = Set[Var]()
  val x = new Var("X", i)
  val a = new Var("a", i)
  usedVars += x

  //p(X) |- q(a)     with    q(X) |- 
  val leftSeq = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a))
  val rightSeq = Sequent(App(Var("q", i -> i), x))()

  val leftNode = new Axiom(leftSeq)
  val rightNode = new Axiom(rightSeq)

  val ur = UnifyingResolution(leftNode, rightNode)(usedVars)

  //Test case 2
  val y = new Var("Y", i)
  usedVars += y
  val leftSeqB = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a))
  val rightSeqB = Sequent(App(Var("q", i -> i), y))()
  val leftNodeB = new Axiom(leftSeqB)
  val rightNodeB = new Axiom(rightSeqB)
  val urB = UnifyingResolution(leftNodeB, rightNodeB)(usedVars)

  //Test case 3
  var b = new Var("B", i)
  usedVars += b
  val leftSeqC = Sequent()(App(App(Var("le", i -> (i -> o)), b), b))
  var u = new Var("U", i)
  var v = new Var("V", i)
  var w = new Var("W", i)
  val rightSeqC = Sequent(App(App(Var("le", i -> (i -> o)), AppRec(new Var("max", i -> (i -> i)), List(u, v))), w))(App(App(Var("le", i -> (i -> o)), v), w))
  usedVars += u
  usedVars += v
  usedVars += w

  val leftNodeC = new Axiom(leftSeqC)
  val rightNodeC = new Axiom(rightSeqC)
  val urC = UnifyingResolution(leftNodeC, rightNodeC)(usedVars)

  class FindDesiredTest extends FindDesiredSequent {
  }

  val tester = new FindDesiredTest
  //tester.checkHalf(computed, desired)
  var c = new Var("c", i)
  var d = new Var("d", i)
  val findSeqTest1A = Sequent()(App(App(Var("a", i -> (i -> i)), c), u))
  val findSeqTest1B = Sequent()(App(App(Var("a", i -> (i -> i)), v), d))
  
  val findSeqTest2A = Sequent()(App(App(Var("a", i -> (i -> i)), c), u))
  val findSeqTest2B = Sequent()(App(App(Var("a", i -> (i -> i)), c), d))

  val findSeqTest3A = Sequent()(App(App(Var("a", i -> (i -> i)), c), u))
  val findSeqTest3B = Sequent()(App(App(Var("a", i -> (i -> i)), c), v))

  val findSeqTest4A = Sequent()(App(App(Var("a", i -> (i -> i)), v), u))
  val findSeqTest4B = Sequent()(App(App(Var("a", i -> (i -> i)), v), u))
  
  val findSeqTest5A = Sequent(App(Var("q", i -> i), x))()
  val findSeqTest5B = App(Var("q", i -> i),v) +: Sequent(App(Var("q", i -> i), u))()  

  
  val findSeqTest6A = App(Var("p", i -> i),x) +: App(Var("q", i -> i),v) +: Sequent(App(Var("q", i -> i), u))()
  val findSeqTest6B = App(Var("p", i -> i),x) +: App(Var("p", i -> i),v) +: Sequent(App(Var("q", i -> i), u))()
 
  "UnifyingResolution" should {
    "return the correct resolvent when necessary to make a substitution" in {
      Sequent(App(Var("p", i -> i), Var("NEW0", i)))() must beEqualTo(ur.conclusion)
    }
    "return the correct resolvent when no substituion necessary" in {
      Sequent(App(Var("p", i -> i), x))() must beEqualTo(urB.conclusion)
    }
    "return the correct resolvent taken from the example" in {
      Sequent()(App(App(Var("le", i -> (i -> o)), v), AppRec(new Var("max", i -> (i -> i)), List(u, v)))) must beEqualTo(urC.conclusion)
    }
  }
  "FindDesiredSequent" should {
    "check that a unification is not applied (2 specific vars)" in {
      tester.checkHalf(findSeqTest1A.suc, findSeqTest1B.suc)(usedVars) must beEqualTo(false)
    }
    "check that a unification is not applied (1 specific var)" in {
      tester.checkHalf(findSeqTest2A.suc, findSeqTest2B.suc)(usedVars) must beEqualTo(false)
    }
    "check that they're equal mod renaming (1 specific var)" in {
      tester.checkHalf(findSeqTest3A.suc, findSeqTest3B.suc)(usedVars) must beEqualTo(true)
    }
    "check that they're equal mod renaming (2 universal vars)" in {
      tester.checkHalf(findSeqTest4A.suc, findSeqTest4B.suc)(usedVars) must beEqualTo(true)
    }
    "check that they're equal mod renaming (different length)" in {
      tester.checkHalf(findSeqTest5A.ant, findSeqTest5B.ant)(usedVars) must beEqualTo(false)
    }    
    "check that they're equal mod renaming (different distribution of formulas)" in {
      tester.checkHalf(findSeqTest6A.ant, findSeqTest6B.ant)(usedVars) must beEqualTo(false)
    }      
  }
}