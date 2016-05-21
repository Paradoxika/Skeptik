package at.logic.skeptik.proof.sequent
package resolution

import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import collection.immutable.Set
import collection.mutable.{ HashMap => MMap, Set => MSet }
import at.logic.skeptik.expression.substitution.immutable.Substitution

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class UnifyingResolutionSpecification extends SpecificationWithJUnit with FindsVars with FindDesiredSequent {

  var usedVars = MSet[Var]()
  val x = new Var("X", i)
  val a = new Var("a", i)
  usedVars += x
  val y = new Var("Y", i)
  usedVars += y

  //The following code is used to test the following methods:
  //conclusionContext
  //mgu
  //rightPremise
  //leftPremise
  //auxL
  //auxR  
  //leftAuxFormulas
  //rightAuxFormulas  
  val URleftSeq = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a))
  val URrightSeq = Sequent(App(Var("q", i -> i), x))()
  val URleftNode = new Axiom(URleftSeq)
  val URrightNode = new Axiom(URrightSeq)
  val URur = UnifyingResolution(URleftNode, URrightNode)(usedVars)

  //leftClean -- no shared
  val URleftSeqB = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a))
  val URrightSeqB = Sequent(App(Var("q", i -> i), y))()
  val URleftNodeB = new Axiom(URleftSeqB)
  val URrightNodeB = new Axiom(URrightSeqB)
  val URurB = UnifyingResolution(URleftNodeB, URrightNodeB)(usedVars)

  //leftClean -- shared
  val URleftSeqC = Sequent(App(Var("p", i -> i), y))(App(Var("q", i -> i), a))
  val URrightSeqC = Sequent(App(Var("q", i -> i), y))()
  val URleftNodeC = new Axiom(URleftSeqC)
  val URrightNodeC = new Axiom(URrightSeqC)
  val URurC = UnifyingResolution(URleftNodeC, URrightNodeC)(usedVars)

  //object (apply) tests
  //p(X) |- q(a)     with    q(X) |- 
  val leftSeq = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a))
  val rightSeq = Sequent(App(Var("q", i -> i), x))()

  val leftNode = new Axiom(leftSeq)
  val rightNode = new Axiom(rightSeq)

  val ur = UnifyingResolution(leftNode, rightNode)(usedVars)

  //Test case 2
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
  var z = new Var("Z", i)
  val rightSeqC = Sequent(App(App(Var("le", i -> (i -> o)), AppRec(new Var("max", i -> (i -> i)), List(u, v))), w))(App(App(Var("le", i -> (i -> o)), v), w))
  usedVars += u
  usedVars += v
  usedVars += w
  usedVars += z
  val leftNodeC = new Axiom(leftSeqC)
  val rightNodeC = new Axiom(rightSeqC)
  val urC = UnifyingResolution(leftNodeC, rightNodeC)(usedVars)

  // test apply with a desired sequent
  val leftNodeD = Axiom(Sequent()(App(Var("p", i -> i), x)))
  val rightNodeD = Axiom(Sequent(App(Var("p", i -> i), y))(App(Var("q", i -> i), z)))
  val desiredD = Sequent()(App(Var("q", i -> i), z))
  val urD = UnifyingResolution(leftNodeD, rightNodeD, desiredD)(usedVars)

  val desiredE = Sequent()(App(Var("q", i -> i), a))

  //test unapply
  val resultF = urD match {
    case u: UnifyingResolution => true
    case _ => false
  }

  class FindDesiredTest extends FindDesiredSequent {
  }

  val tester = new FindDesiredTest

  //empty pairs
  val FDSpairsA = Seq[(E, E)]()
  val FDSdesiredA = Sequent()() //doesn't matter
  val FDSleftA = Axiom(Sequent()())
  val FDSrightA = Axiom(Sequent()())
  val FDSleftCleanA = Axiom(Sequent()())

  //requires no recursive call
  val FDSpairsB = Seq[(E, E)]((App(Var("p", i -> i), x), App(Var("p", i -> i), y)))
  val FDSdesiredB = Sequent()()
  val FDSleftB = Axiom(Sequent()(App(Var("p", i -> i), x)))
  val FDSrightB = Axiom(Sequent(App(Var("p", i -> i), y))())
  val FDSleftCleanB = FDSleftB

  val FDSresultB = tester.findDesiredSequent(FDSpairsB, FDSdesiredB, FDSleftB, FDSrightB, FDSleftCleanB, false)(usedVars)
  val FDSexpectedB = UnifyingResolution(FDSleftB, FDSrightB)(usedVars)

  //requires recursive call
  val FDSpairsC = Seq[(E, E)]((App(Var("p", i -> i), x), App(Var("p", i -> i), z))) ++ Seq[(E, E)]((App(Var("q", i -> i), a), App(Var("q", i -> i), y)))
  val FDSdesiredC = Sequent(App(Var("p", i -> i), y))(App(Var("p", i -> i), x))
  val FDSleftC = Axiom(Sequent()(App(Var("p", i -> i), x)) + App(Var("q", i -> i), a))
  val FDSrightC = Axiom(App(Var("q", i -> i), y) +: Sequent(App(Var("p", i -> i), z))())
  val FDSleftCleanC = FDSleftC
  val FDSresultC = tester.findDesiredSequent(FDSpairsC, FDSdesiredC, FDSleftC, FDSrightC, FDSleftCleanC, false)(usedVars)
  val FDSexpectedC = Sequent(App(Var("p", i -> i), z))(App(Var("p", i -> i), x))

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
  val emptyMap = MMap[Var, Set[E]]()

  val aMap = MMap[Var, Set[E]]()
  aMap.put(x, Set[E](y))

  val bMap = MMap[Var, Set[E]]()
  bMap.put(y, Set[E](x))

  val cMap = MMap[Var, Set[E]]()
  cMap.put(x, Set[E](y))
  cMap.put(y, Set[E](x))

  val dMap = MMap[Var, Set[E]]()
  dMap.put(x, Set[E]())

  val eMap = MMap[Var, Set[E]]()
  eMap.put(x, Set[E](x) + y)

  //checkHelperAlphaManual
  //true
  val chSeq1A = Seq[E](App(Var("q", i -> i), x))
  val chSeq1B = Seq[E](App(Var("q", i -> i), y))

  //false
  val chSeq2A = Seq[E](App(Var("q", i -> i), x))
  val chSeq2B = Seq[E](App(Var("q", i -> i), c))

  //true
  val chSeq4A = Seq[E](App(Var("q", i -> i), x)) ++ Seq[E](App(Var("p", i -> i), u))
  val chSeq4B = Seq[E](App(Var("q", i -> i), y)) ++ Seq[E](App(Var("p", i -> i), u))

  //false
  val chSeq5A = Seq[E](App(Var("q", i -> i), x)) ++ Seq[E](App(Var("p", i -> i), u))
  val chSeq5B = Seq[E](App(Var("q", i -> i), y)) ++ Seq[E](App(Var("p", i -> i), u)) ++ Seq[E](App(Var("p", i -> i), v))

  //false
  val chSeq6A = Seq[E](App(Var("q", i -> i), x)) ++ Seq[E](App(Var("p", i -> i), u)) ++ Seq[E](App(Var("p", i -> i), v))
  val chSeq6B = Seq[E](App(Var("q", i -> i), y)) ++ Seq[E](App(Var("p", i -> i), u))

  //false
  val chSeq7A = Seq[E](App(Var("q", i -> i), x)) ++ Seq[E](App(Var("p", i -> i), u))
  val chSeq7B = Seq[E](App(Var("q", i -> i), y)) ++ Seq[E](App(Var("p", i -> i), u)) ++ Seq[E](App(Var("p", i -> i), c))

  //checkSubstitutions
  val varToAbsSub = Substitution((x, App(Var("a", i -> (i -> i)), c)))
  val varToVar = Substitution((x, y))
  val varToSVar = Substitution((x, c))
  val varToSVars = Substitution((x, c), (y, x))
  val varToSVarE = Substitution((x, c), (y, App(Var("a", i -> (i -> i)), c)))
  val varToSVarEVar = Substitution((x, c), (y, App(Var("a", i -> (i -> i)), u)))
  val varToVars = Substitution((x, y), (y, x))

  //generateSubstitutionOptions
  //empty map
  val gsSeq1A = Seq[E](App(Var("q", i -> i), d))
  val gsSeq1B = Seq[E](App(Var("q", i -> i), c))

  //empty map
  val gsSeq2A = Seq[E](App(Var("q", i -> i), x))
  val gsSeq2B = Seq[E](App(Var("p", i -> i), y))

  val gsMap3 = MMap[Var, Set[Var]]()
  gsMap3.put(x, Set[Var](y))
  val gsSeq3A = Seq[E](App(Var("q", i -> i), x))
  val gsSeq3B = Seq[E](App(Var("q", i -> i), y))

  val gsMap4 = MMap[Var, Set[Var]]()
  gsMap4.put(x, Set[Var](y) + u)
  val gsSeq4A = Seq[E](App(Var("q", i -> i), x))
  val gsSeq4B = Seq[E](App(Var("q", i -> i), y)) ++ Seq[E](App(Var("q", i -> i), u))

  val gsMap5 = MMap[Var, Set[Var]]()
  gsMap5.put(x, Set[Var](y))
  gsMap5.put(u, Set[Var](v))
  val gsSeq5A = Seq[E](App(Var("q", i -> i), x)) ++ Seq[E](App(Var("p", i -> i), u))
  val gsSeq5B = Seq[E](App(Var("q", i -> i), y)) ++ Seq[E](App(Var("p", i -> i), v))

  val gsMap6 = MMap[Var, Set[Var]]()
  gsMap6.put(x, Set[Var](y))
  gsMap6.put(u, Set[Var]( Var("1", i) ))
  val gsSeq6A = Seq[E](App(Var("q", i -> i), x)) ++ Seq[E](App(Var("p", i -> i), u))
  val gsSeq6B = Seq[E](App(Var("q", i -> i), y)) ++ Seq[E](App(Var("p", i -> i), Var("1", i)))

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

  //getSetOfVars - proof node (overloaded method not tested; inputs would be the same but passed in differently)
  val vAc = new Axiom(Sequent(App(Var("a", i -> (i -> i)), c))())

  val vAX = new Axiom(Sequent(App(Var("a", i -> (i -> i)), x))())

  val vAcX = new Axiom(App(Var("a", i -> (i -> i)), x) +: Sequent(App(Var("a", i -> (i -> i)), x))())

  val vAXY = new Axiom(Sequent(App(Var("a", i -> (i -> i)), x))(App(Var("b", i -> (i -> i)), y)))

  val vAX1 = new Axiom(Sequent(App(Var("a", i -> (i -> i)), x))(App(Var("b", i -> (i -> i)), Var("1", i))))

  //CanRenameVariables----
  class Renamer extends CanRenameVariables {
  }
  val renameTester = new Renamer
  //fixSharedNoFilter
  //1 empty node
  val rename1lefta = Axiom(Sequent()())
  val rename1righta = Axiom(Sequent()(App(Var("p", i -> i), z)))
  val rename1expecteda = rename1lefta
  val rename1outa = renameTester.fixSharedNoFilter(rename1lefta, rename1righta, 0, usedVars)

  //1 shared variable
  val rename1leftb = Axiom(Sequent()(App(Var("q", i -> i), z)))
  val rename1rightb = Axiom(Sequent()(App(Var("p", i -> i), z)))
  val rename1expectedb = Axiom(Sequent()(App(Var("q", i -> i), Var("NEW0", i)))).conclusion
  val rename1outb = renameTester.fixSharedNoFilter(rename1leftb, rename1rightb, 0, usedVars).conclusion
  val rename1bFinal = findRenaming(rename1expectedb, rename1outb)(usedVars) != null

  //2 shared variables
  val rename1leftc = Axiom(Sequent(App(Var("q", i -> i), y))(App(Var("q", i -> i), z)))
  val rename1rightc = Axiom(Sequent(App(Var("q", i -> i), y))(App(Var("p", i -> i), z)))
  val rename1expectedc = Axiom(Sequent(App(Var("q", i -> i), x))(App(Var("q", i -> i), Var("NEW0", i)))).conclusion
  val rename1outc = renameTester.fixSharedNoFilter(rename1leftc, rename1rightc, 0, usedVars).conclusion
  val rename1cFinal = findRenaming(rename1expectedc, rename1outc)(usedVars) != null

  //no shared variables
  val rename1leftd = Axiom(Sequent()(App(Var("p", i -> i), x)))
  val rename1rightd = Axiom(Sequent()(App(Var("p", i -> i), z)))
  val rename1expectedd = rename1leftd
  val rename1outd = renameTester.fixSharedNoFilter(rename1leftd, rename1rightd, 0, usedVars)

  //isUnifiable
  val rename2a = (App(Var("p", i -> i), x), App(Var("p", i -> i), z))
  val rename2b = (App(Var("p", i -> i), x), App(Var("q", i -> i), z))
  val rename2c = (App(Var("p", i -> i), a), App(Var("p", i -> i), z))
  val rename2d = (App(Var("p", i -> i), x), App(Var("p", i -> i), Var("1", i)))

  "CanRenameVariables" should {
    "not worry about shared variables if one node is empty" in {
      rename1outa must beEqualTo(rename1expecteda)
    }
    "handle 1 shared variable correctly" in {
      rename1bFinal must beEqualTo(true)
    }
    "handle 2 shared variables correctly" in {
      rename1cFinal must beEqualTo(true)
    }
    "handle 0 shared variables correctly" in {
      rename1outd must beEqualTo(rename1expectedd)
    }
    "report true for unifiable pair" in {
      renameTester.isUnifiable(rename2a)(usedVars) must beEqualTo(true)
    }
    "report false for non-unifiable pair" in {
      renameTester.isUnifiable(rename2b)(usedVars) must beEqualTo(false)
    }
    "report true for unifiable pair (specific)" in {
      renameTester.isUnifiable(rename2c)(usedVars) must beEqualTo(true)
    }
    "report true for unifiable pair (specific number)" in {
      renameTester.isUnifiable(rename2d)(usedVars) must beEqualTo(true)
    }
  }
  "UnifyingResolution" should {
    "return the correct resolvent when necessary to make a substitution" in {
      findRenaming(Sequent(App(Var("p", i -> i), Var("NEW0", i)))(), ur.conclusion)(usedVars) != null must beEqualTo(true)
    }
    "return the correct resolvent when no substituion necessary" in {
      Sequent(App(Var("p", i -> i), x))() must beEqualTo(urB.conclusion)
    }
    "return the correct resolvent taken from the example" in {
      Sequent()(App(App(Var("le", i -> (i -> o)), v), AppRec(new Var("max", i -> (i -> i)), List(u, v)))) must beEqualTo(urC.conclusion)
    }
    "return the desired resolvent" in {
      desiredD must beEqualTo(urD.conclusion)
    }
    "throw an exception if the desired sequent can't be found" in {
      UnifyingResolution(leftNodeD, rightNodeD, desiredE)(usedVars) must throwA[Exception]
    }
    "implement unapply correctly" in {
      resultF must beEqualTo(true)
    }
    "return the correct leftPremise" in {
      URur.leftPremise must beEqualTo(URleftNode)
    }
    "return the correct rightPremise" in {
      URur.rightPremise must beEqualTo(URrightNode)
    }
    "return the correct clean left (no shared)" in {
      URurB.leftClean must beEqualTo(URleftNodeB)
    }
    "return the correct clean left (shared)" in {
      findRenaming(URurC.leftClean.conclusion, URleftNodeC.conclusion)(usedVars) != null must beEqualTo(true)
    }
    "return the correct auxL" in {
      findRenaming(Sequent()(URur.auxL), Sequent()(App(Var("q", i -> i), a)))(usedVars) != null must beEqualTo(true)
    }
    "return the correct auxR" in {
      findRenaming(Sequent()(URur.auxR), Sequent()(App(Var("q", i -> i), y)))(usedVars) != null must beEqualTo(true)
    }
    "return the correct leftAuxFormulas" in {
      findRenaming(URur.leftAuxFormulas, Sequent()(App(Var("q", i -> i), a)))(usedVars) != null must beEqualTo(true)
    }
    "return the correct rightAuxFormulas" in {
      findRenaming(URur.rightAuxFormulas, Sequent(App(Var("q", i -> i), y))())(usedVars) != null must beEqualTo(true)
    }
    "return the correct mgu" in {
      URur.mgu must beEqualTo(Substitution((x, a)))
    }
    "return the correct conclusion context" in {
      findRenaming(URur.conclusionContext, Sequent(App(Var("p", i -> i), y))())(usedVars) != null must beEqualTo(true)
    }
  }
  "FindDesiredSequent" should {
    "Throw an exception as the recursive base case" in {
      tester.findDesiredSequent(FDSpairsA, FDSdesiredA, FDSleftA, FDSrightA, FDSleftCleanA, false)(usedVars) must throwA[Exception]
    }
    "Handle an easy case (no recursion) in finding the desired sequent" in {
      FDSexpectedB.asInstanceOf[UnifyingResolution].conclusion.equals(FDSresultB.conclusion) must beEqualTo(true)
    }
    "Recurse correctly in finding the desired sequent" in {
      FDSresultC.conclusion must beEqualTo(FDSexpectedC)
    }
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
      tester.findRenaming(findSeqTest7A, findSeqTest7B)(usedVars) != null must beEqualTo(false)
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
      tester.validMap(emptyMap, usedVars) must beEqualTo(true)
    }
    "valid map correctly checks empty var set" in {
      tester.validMap(dMap, usedVars) must beEqualTo(false)
    }
    "valid map correctly checks nonempty var set" in {
      tester.validMap(aMap, usedVars) must beEqualTo(true)
    }
    "check substitution correctly checks righthand side is var (false)" in {
      tester.checkSubstitutions(varToAbsSub) must beEqualTo(false)
    }
    "check substitution correctly checks righthand side is var (true)" in {
      tester.checkSubstitutions(varToVar) must beEqualTo(true)
    }
    "check substitution correctly checks righthand side is a universal var" in {
      tester.checkSubstitutions(varToSVar) must beEqualTo(false)
    }
    "check substitution correctly checks righthand side is var (many right hand sides; one true, one false)" in {
      tester.checkSubstitutions(varToSVars) must beEqualTo(false)
    }
    "check substitution correctly checks righthand side is var (many right; one non-var)" in {
      tester.checkSubstitutions(varToSVarE) must beEqualTo(false)
    }
    "check substitution correctly checks righthand sides (many right; none good)" in {
      tester.checkSubstitutions(varToSVarEVar) must beEqualTo(false)
    }
    "check substitution correctly checks righthand sides (many right; all good)" in {
      tester.checkSubstitutions(varToVars) must beEqualTo(true)
    }
    "generateSubstitutionOptions should return the empty map" in {
      tester.generateSubstitutionOptions(gsSeq1A, gsSeq1B) must beEqualTo(emptyMap)
    }
    "generateSubstitutionOptions should return the empty map" in {
      tester.generateSubstitutionOptions(gsSeq2A, gsSeq2B) must beEqualTo(emptyMap)
    }
    "generateSubstitutionOptions should return the correct map" in {
      tester.generateSubstitutionOptions(gsSeq3A, gsSeq3B) must beEqualTo(gsMap3)
    }
    "generateSubstitutionOptions should return the correct map" in {
      tester.generateSubstitutionOptions(gsSeq4A, gsSeq4B) must beEqualTo(gsMap4)
    }
    "generateSubstitutionOptions should return the correct map" in {
      tester.generateSubstitutionOptions(gsSeq5A, gsSeq5B) must beEqualTo(gsMap5)
    }
    "generateSubstitutionOptions should return the correct map" in {
      tester.generateSubstitutionOptions(gsSeq6A, gsSeq6B) must beEqualTo(gsMap6)
    }
    "checkHelperAlphaManual should return the correct result (x->y; true)" in {
      tester.checkHelperAlphaManual(chSeq1A, chSeq1B)(usedVars) must beEqualTo(true)
    }
    "checkHelperAlphaManual should return the correct result (x->c; false)" in {
      tester.checkHelperAlphaManual(chSeq2A, chSeq2B)(usedVars) must beEqualTo(false)
    }
    "checkHelperAlphaManual should return the correct result (even distribution)" in {
      tester.checkHelperAlphaManual(chSeq4A, chSeq4B)(usedVars) must beEqualTo(true)
    }
    "checkHelperAlphaManual should return the correct result (longer desired)" in {
      tester.checkHelperAlphaManual(chSeq5A, chSeq5B)(usedVars) must beEqualTo(false)
    }
    "checkHelperAlphaManual should return the correct result (longer computed)" in {
      tester.checkHelperAlphaManual(chSeq6A, chSeq6B)(usedVars) must beEqualTo(false)
    }
    "checkHelperAlphaManual should return the correct result (number in desired; longer)" in {
      tester.checkHelperAlphaManual(chSeq7A, chSeq7B)(usedVars) must beEqualTo(false)
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