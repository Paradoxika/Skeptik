package at.logic.skeptik.proof.sequent
package resolution

import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import collection.immutable.Set
import collection.mutable.{ HashMap => MMap, Set => MSet }

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class UnifyingResolutionSpecification extends SpecificationWithJUnit with FindsVars {

  var usedVars = MSet[Var]()
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

  //println("Are they alpha equal? " + (App(App(Var("a", i -> (i -> i)), c), u) =+= App(App(Var("a", i -> (i -> i)), c), v)))

  val findSeqTest4A = Sequent()(App(App(Var("a", i -> (i -> i)), v), u))
  val findSeqTest4B = Sequent()(App(App(Var("a", i -> (i -> i)), v), u))

  val findSeqTest5A = Sequent(App(Var("q", i -> i), x))()
  val findSeqTest5B = App(Var("q", i -> i), v) +: Sequent(App(Var("q", i -> i), u))()

  val findSeqTest6A = App(Var("p", i -> i), x) +: App(Var("q", i -> i), v) +: Sequent(App(Var("q", i -> i), u))()
  val findSeqTest6B = App(Var("p", i -> i), x) +: App(Var("p", i -> i), v) +: Sequent(App(Var("q", i -> i), u))()

  //desiredFound tests
  val findSeqTest7A = App(Var("p", i -> i), x) +: App(Var("q", i -> i), y) +: (Sequent()(App(Var("r", i -> i), y)) + App(Var("s", i -> i), x))
  val findSeqTest7B = App(Var("p", i -> i), u) +: App(Var("q", i -> i), v) +: (Sequent()(App(Var("r", i -> i), u)) + App(Var("s", i -> i), v))

  //intersectionMap
  val emptyMap = MMap[Var, Set[Var]]()

  val aMap = MMap[Var, Set[Var]]()
  aMap.put(x, Set[Var](y))

  val bMap = MMap[Var, Set[Var]]()
  bMap.put(y, Set[Var](x))

  val cMap = MMap[Var, Set[Var]]()
  cMap.put(x, Set[Var](y))
  cMap.put(y, Set[Var](x))

  val dMap = MMap[Var, Set[Var]]()
  dMap.put(x, Set[Var]())  
  
  val eMap = MMap[Var, Set[Var]]()
  eMap.put(x, Set[Var](x) + y) 
  
  //checkHelperAlphaManual

  //checkSubstitutions

  //generateSubstitutionOptions
  
  //validMap
  //uses above
  

  //------checkUnifiableVariableName trait tests
  //isValidName
  class ValidNameTest extends checkUnifiableVariableName {
  }
  val nameTester = new ValidNameTest

  
  //------FindsVars trait tests  
  class varsTest extends FindsVars {
  }
  val varsTester = new varsTest
    
  //getSetOfVars - proof node
  val vAc = new Axiom(Sequent(App(Var("a", i -> (i -> i)), c))())
  
  val vAX = new Axiom(Sequent(App(Var("a", i -> (i -> i)), x))())
  
  val vAcX = new Axiom(App(Var("a", i -> (i -> i)), x) +: Sequent(App(Var("a", i -> (i -> i)), x))())
  
  val vAXY = new Axiom(Sequent(App(Var("a", i -> (i -> i)), x))(App(Var("b", i -> (i -> i)), y)))
  
  val vAX1 = new Axiom(Sequent(App(Var("a", i -> (i -> i)), x))(App(Var("b", i -> (i -> i)), Var("1", i))))
  
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
    "check that a unification is not applied for a sequent half (2 specific vars)" in {
      tester.checkHalf(findSeqTest1A.suc, findSeqTest1B.suc)(usedVars) must beEqualTo(false)
    }
    "check that a unification is not applied for a sequent half (1 specific var)" in {
      tester.checkHalf(findSeqTest2A.suc, findSeqTest2B.suc)(usedVars) must beEqualTo(false)
    }
    "check that they're equal mod renaming for a sequent half(1 specific var)" in {
      tester.checkHalf(findSeqTest3A.suc, findSeqTest3B.suc)(usedVars) must beEqualTo(true)
    }
    "check that they're equal mod renaming for a sequent half (2 universal vars)" in {
      tester.checkHalf(findSeqTest4A.suc, findSeqTest4B.suc)(usedVars) must beEqualTo(true)
    }
    "check that they're equal mod renaming for a sequent half (different length)" in {
      tester.checkHalf(findSeqTest5A.ant, findSeqTest5B.ant)(usedVars) must beEqualTo(false)
    }
    "check that they're equal mod renaming for a sequent half (different distribution of formulas)" in {
      tester.checkHalf(findSeqTest6A.ant, findSeqTest6B.ant)(usedVars) must beEqualTo(false)
    }
    "check that they're equal mod renaming for an entire sequent (different distribution of formulas)" in {
      tester.desiredFound(findSeqTest7A, findSeqTest7B)(usedVars) must beEqualTo(false)
    }
    "intersect maps correctly (2 empty maps)" in {
      tester.intersectMaps(emptyMap, emptyMap) must beEqualTo(emptyMap)
    }
    "intersect maps correctly (1 empty map)" in {
      tester.intersectMaps(aMap, emptyMap) must beEqualTo(aMap)
    }
    "intersect maps correctly (0 empty maps; disjoint)" in {
      tester.intersectMaps(aMap, bMap) must beEqualTo(cMap)
    }
    "intersect maps correctly (0 empty maps; the same)" in {
      tester.intersectMaps(aMap, aMap) must beEqualTo(aMap)
    }
    "intersect maps correctly (0 empty maps; 1 var's set is empty)" in {
      tester.intersectMaps(aMap, dMap) must beEqualTo(dMap)
    }
    "intersect maps correctly (0 empty maps; no var's set is empty)" in {
      tester.intersectMaps(aMap, eMap) must beEqualTo(aMap)
    }   
    "valid map correctly checks empty map" in {
      tester.validMap(emptyMap) must beEqualTo(true)
    }  
    "valid map correctly checks empty var set" in {
      tester.validMap(dMap) must beEqualTo(false)
    } 
    "valid map correctly checks nonempty var set" in {
      tester.validMap(aMap) must beEqualTo(true)
    }     
  }
  "checkUnifiableVariableName" should {
    "return true for X" in {
      nameTester.isValidName(x) must beEqualTo(true)
    }
    "return true for Xa" in {
      nameTester.isValidName(new Var("Xa", o)) must beEqualTo(true)
    }
    "return false for y" in {
      nameTester.isValidName(new Var("y", o)) must beEqualTo(false)
    }
    "return false for yA" in {
      nameTester.isValidName(new Var("yA", o)) must beEqualTo(false)
    }
    "return false for 3" in {
      nameTester.isValidName(new Var("3", o)) must beEqualTo(false)
    }
  }
  "FindsVars" should {
    "ignore lowercase vars" in {
      varsTester.getSetOfVars(vAc) must beEqualTo(Set[Var]())
    }
    "capture uppercase vars" in {
      varsTester.getSetOfVars(vAX) must beEqualTo(Set[Var](x))
    }
    "ignore lowercase vars & capture uppercase vars" in {
      varsTester.getSetOfVars(vAcX) must beEqualTo(Set[Var](x))
    }
    "capture multiple upper case vars" in {
      varsTester.getSetOfVars(vAXY) must beEqualTo((Set[Var](x) + y))
    }
    "ignore numbers vars" in {
      varsTester.getSetOfVars(vAX1) must beEqualTo(Set[Var](x))
    }    
  }
}