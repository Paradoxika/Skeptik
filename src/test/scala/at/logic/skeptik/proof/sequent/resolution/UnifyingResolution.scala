package at.logic.skeptik.proof.sequent
package resolution

import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import collection.immutable.Set
import collection.mutable.{ HashMap => MMap, Set => MSet }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.expression.formula.Atom

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
    case _                     => false
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
  gsMap6.put(u, Set[Var](Var("1", i)))
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
  println("..........................")
  val rename1cFinal = findRenaming(rename1expectedc, rename1outc)(usedVars) != null
  println("..........................")

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

  //July 28 Tests
  /*
     * 	java.lang.Exception: Resolution: Cannot find desired resolvent
				Desired: (p5 V-290), (p5 V-290) ⊢
				leftPremise: (p5 V-290) ⊢ (p10 V-292 V-293)
				rightPremise: (p5 V-290), (p10 V-291 c2) ⊢
     */
  val v290 = new Var("V-290", i)
  usedVars += v290
  val v291 = new Var("V-291", i)
  usedVars += v291
  val v292 = new Var("V-292", i)
  usedVars += v292
  val v293 = new Var("V-293", i)
  usedVars += v293

  val p10 = App(App(Var("p10", i -> (i -> i)), v292), v293)
  val p10c = App(App(Var("p10", i -> (i -> i)), v291), new Var("c2", i))
  val p5 = App(Var("p5", i -> (i -> i)), v290)

  val l = new Axiom(Sequent(p5)(p10))
  val r = new Axiom(p10c +: Sequent(p5)())

  println("L: " + l)
  println("R: " + r)
  val d1 = p5 +: Sequent(p5)()

  val urNoD = UnifyingResolution(l, r)(usedVars)
  println("no desired: " + urNoD)

  val ur1 = UnifyingResolution(l, r, d1)(usedVars)

  //(p5 X), (p5 V-290) ⊢ 
  val p5b = App(Var("p5", i -> (i -> i)), x)
  val ac1 = p5 +: Sequent(p5b)()

  println("ur1: " + ur1)
  println("ac1: " + ac1)
  println("desired1: " + d1)

  /*
    	Desired: (p10 V-0), (p9 V-2), (p11 c4 V-113), (p2 V-176), (p13 V-202 V-203), (p11 V-219 V-113) ⊢
			leftPremise: (p2 V-176), (p13 V-202 V-203), (p11 V-219 V-113) ⊢ (p8 V-223 V-224 V-225 V-226)
			rightPremise: (p10 V-0), (p9 V-2), (p11 c4 V-113), (p8 V-220 V-221 V-222 c4) ⊢
    */

  val v0 = new Var("V-0", i)
  usedVars += v0
  val v2 = new Var("V-2", i)
  usedVars += v2
  val v113 = new Var("V-113", i)
  usedVars += v113
  val v176 = new Var("V-176", i)
  usedVars += v176
  val v202 = new Var("V-202", i)
  usedVars += v202
  val v203 = new Var("V-203", i)
  usedVars += v203
  val v219 = new Var("V-219", i)
  usedVars += v219
  val v223 = new Var("V-223", i)
  usedVars += v223
  val v224 = new Var("V-224", i)
  usedVars += v224
  val v225 = new Var("V-225", i)
  usedVars += v225
  val v226 = new Var("V-226", i)
  usedVars += v226
  val v220 = new Var("V-220", i)
  usedVars += v220
  val v221 = new Var("V-221", i)
  usedVars += v221
  val v222 = new Var("V-222", i)
  usedVars += v222

  //(p2 V-176), (p13 V-202 V-203), (p11 V-219 V-113) ⊢ (p8 V-223 V-224 V-225 V-226)
  val p2 = App(Var("p2", i -> (i -> i)), v176)
  val p13 = App(App(Var("p13", i -> (i -> i)), v202), v203)
  val p11 = App(App(Var("p11", i -> (i -> i)), v219), v113)
  val p8 = App(App(App(App(Var("p10", i -> (i -> (i -> (i -> i)))), v223), v224), v225), v226)

  val l2 = Axiom(p2 +: (p13 +: Sequent(p11)(p8)))

  //(p10 V-0), (p9 V-2), (p11 c4 V-113), (p8 V-220 V-221 V-222 c4) ⊢
  val p10f = App(Var("p10", i -> (i -> i)), v0)
  val p9 = App(Var("p9", i -> (i -> i)), v2)
  val p11b = App(App(Var("p11", i -> (i -> i)), new Var("c4", i)), v113)
  val p8b = App(App(App(App(Var("p10", i -> (i -> (i -> (i -> i)))), v220), v221), v222), new Var("c4", i))
  val r2 = Axiom(p10f +: (p9 +: (p11b +: (Sequent(p8b)()))))

  //(p10 V-0), (p9 V-2), (p11 c4 V-113), (p2 V-176), (p13 V-202 V-203), (p11 V-219 V-113) ⊢
  val d2 = p10f +: (p9 +: (p11b +: (p2 +: (p13 +: Sequent(p11)()))))
  println("L: " + l2)
  println("R: " + r2)
  val ur2 = UnifyingResolution(l2, r2, d2)(usedVars)
  //(p2 V-176), (p13 V-202 V-203), (p11 V-219 X), (p11 c4 V-113), (p9 V-2), (p10 V-0) ⊢ 
  val p11c = App(App(Var("p11", i -> (i -> i)), v219), x)

  val ac2 = p10f +: (p9 +: (p11b +: (p11c +: (p13 +: Sequent(p2)()))))

  println("ur2: " + ur2) //pass
  println("ac2: " + ac2) //pass
  println("D2: " + d2)

  /*
     * 	Desired:  ⊢ (p6 V-235 V-236 V-237), (p1 V-399 V-400), (p1 V-399 V-400)
				leftPremise:  ⊢ (p1 V-399 V-400), (p0 V-401 V-402 V-403 V-404)
				rightPremise: (p0 V-405 V-402 V-406 V-407) ⊢ (p6 V-235 V-236 V-237), (p1 V-399 V-400)
     */
  val v235 = new Var("V-235", i)
  usedVars += v235
  val v236 = new Var("V-236", i)
  usedVars += v236
  val v237 = new Var("V-237", i)
  usedVars += v237
  val v399 = new Var("V-399", i)
  usedVars += v399
  val v400 = new Var("V-400", i)
  usedVars += v400
  val v401 = new Var("V-401", i)
  usedVars += v401
  val v402 = new Var("V-402", i)
  usedVars += v402
  val v403 = new Var("V-403", i)
  usedVars += v403
  val v404 = new Var("V-404", i)
  usedVars += v404
  val v405 = new Var("V-405", i)
  usedVars += v405
  val v406 = new Var("V-406", i)
  usedVars += v406
  val v407 = new Var("V-407", i)
  usedVars += v407
  //leftPremise:  ⊢ (p1 V-399 V-400), (p0 V-401 V-402 V-403 V-404)
  val p1 = App(App(Var("p1", i -> (i -> i)), v399), v400)
  val p0 = App(App(App(App(Var("p0", i -> (i -> (i -> (i -> i)))), v401), v402), v403), v404)

  val l3 = Axiom(Sequent()(p1) + p0)

  //(p0 V-405 V-402 V-406 V-407) ⊢ (p6 V-235 V-236 V-237), (p1 V-399 V-400)
  val p0b = App(App(App(App(Var("p0", i -> (i -> (i -> (i -> i)))), v405), v402), v406), v407)
  val p6 = App(App(App(Var("p6", i -> (i -> (i -> i))), v235), v236), v237)

  val r3 = Axiom(Sequent(p0b)(p6) + p1)

  //⊢ (p6 V-235 V-236 V-237), (p1 V-399 V-400), (p1 V-399 V-400)
  val d3 = Sequent()(p6) + p1 + p1

  println("R: " + r3)
  println("L: " + l3)

  val ur3 = UnifyingResolution(l3, r3, d3)(usedVars)

  //⊢ (p1 X V-222), (p6 V-235 V-236 V-237), (p1 V-399 V-400)
  val p1b = App(App(Var("p1", i -> (i -> i)), x), v222)
  val ac3 = Sequent()(p1b) + p6 + p1
  println("ur3: " + ur3) //pass
  println("ac3: " + ac3) //pass  
  println("D: " + d3)

  /*
     * 	Desired:  ⊢ (p4 c0 V-191), (p4 V-194 V-191)
				leftPremise:  ⊢ (p4 V-194 V-191), (p13 V-195 c3 (f0 V-196 V-197))
				rightPremise: (p13 V-195 c3 (f0 V-198 V-199)) ⊢ (p4 c0 V-191)
     * 
     */
  val v191 = new Var("V-191", i)
  usedVars += v191
  val v194 = new Var("V-194", i)
  usedVars += v194
  val v195 = new Var("V-195", i)
  usedVars += v195
  val v196 = new Var("V-196", i)
  usedVars += v196
  val v197 = new Var("V-197", i)
  usedVars += v197
  val v198 = new Var("V-198", i)
  usedVars += v198
  val v199 = new Var("V-199", i)
  usedVars += v199

  //⊢ (p4 V-194 V-191), (p13 V-195 c3 (f0 V-196 V-197))
  val p4 = App(App(Var("p4", i -> (i -> i)), v194), v191)
  val f0 = App(App(Var("f0", i -> (i -> i)), v196), v197)
  val p13q = App(App(App(Var("p13", i -> (i -> (i -> i))), v195), new Var("c3", i)), f0)
  val l4 = Axiom(Sequent()(p4) + p13q)

  //rightPremise: (p13 V-195 c3 (f0 V-198 V-199)) ⊢ (p4 c0 V-191)
  val f0b = App(App(Var("f0", i -> (i -> i)), v198), v199)
  val p13b = App(App(App(Var("p13", i -> (i -> (i -> i))), v195), new Var("c3", i)), f0b)
  val p4b = App(App(Var("p4", i -> (i -> i)), new Var("c0", i)), v191)

  val r4 = Axiom(Sequent(p13b)(p4b))

  // ⊢ (p4 c0 V-191), (p4 V-194 V-191)
  val d4 = Sequent()(p4) + p4b

  println("L: " + l4)
  println("R: " + r4)
  //    println("D: " + d4)

  val ur4 = UnifyingResolution(l4, r4, d4)(usedVars)

  //⊢ (p4 V-194 V-222), (p4 c0 V-191)
  val p4c = App(App(Var("p4", i -> (i -> i)), v194), v222)
  val ac4 = Sequent()(p4c) + p4b
  println("ac4: " + ac4)
  println("Ur4: " + ur4) //pass
  println("D: " + d4)

  
  
  ///////August 11 2016 Tests Begin
  
    val desiredA11a = Sequent()(Atom("p16",List(Var("V3",i))),
                            Atom("p17",List(Var("V3",i))),
                            Atom("p17",List(Var("V6",i)))
                           )
    val left    = Axiom(Sequent()(Atom("p16",List(Var("V3",i))),
                                  Atom("p19",List(Var("V3",i),Var("V3",i),Var("V6",i)))
                                 )
                       )
    val right   = Axiom(Sequent(Atom("p19",List(Var("V3",i),Var("V3",i),Var("V6",i))))
                               (Atom("p17",List(Var("V3",i))),
                                Atom("p17",List(Var("V6",i)))
                               )
                       )
    val varsa    = MSet[Var](Var("V3",i),Var("V6",i))
    println("L: " + left)
    println("R: " + right)
    val  URA11a = UnifyingResolution(left, right, desiredA11a)(varsa)
    println("UR: " + URA11a)
    println("--------------------------\n\n\n\n")
    
    
    val desiredA11b = Sequent()(Atom("p26",List(Var("V2",i))),
                             Atom("p26",List(Var("V18",i))))
    val left2    = Axiom(Sequent()(Atom("p26",List(Var("V18",i))),
                                  Atom("p27",List(Var("V2",i),Var("V18",i)))
                                 )
                       )
    val right2   = Axiom(Sequent(Atom("p27",List(Var("V2",i),Var("V18",i))))
                               (Atom("p26",List(Var("V2",i))))
                       )
    val varsb    = MSet[Var](Var("V2",i),Var("V18",i))
//    var UR2 = UnifyingResolution(left2,right2)(vars2)
    val URA11b = UnifyingResolution(left2,right2, desiredA11b)(varsb)
    println("L: " + left2)
    println("R: " + right2)
    println("UR: " + URA11b)  
  
    /*
    Desired: (p16 c12), (p16 V6) ⊢ 
		//The following are swapped compared to e-mail
		Right premise: (p17 c12 V6), (p16 V6) ⊢ 
		Left premise: (p16 V7) ⊢ (p17 V7 V6)
    */
      val desiredA11c = Sequent(Atom("p16",List(Var("c12",i))),
                            Atom("p16",List(Var("V6",i))))()
                            
    val rightA11c   = Axiom(Sequent(Atom("p16",List(Var("V6",i))),
                                  Atom("p17",List(Var("c12",i),Var("V6",i)))
                                )())
                                
    val leftA11c   = Axiom(Sequent(Atom("p16",List(Var("V7",i))))
                               (Atom("p17",List(Var("V7",i),Var("V6",i)))
                               )
                       )
    val varsA11c    = MSet[Var](Var("V3",i),Var("V7",i),Var("V6",i))
    println("L: " + leftA11c)
    println("R: " + rightA11c)
        println("Initial desired: " + desiredA11c)

    val  URA11c = UnifyingResolution(leftA11c, rightA11c, desiredA11c)(varsA11c)  
  
    /*
 * 	Desired: (p15 (f9 V20 V3)), (p15 (f9 V18 V19)) ⊢ (p25 V20)
		leftPremise: (p15 (f9 V18 V19)), (p15 (f9 V20 V3)) ⊢ (p20 V22), (p25 V20)
		rightPremise: (p20 c15) ⊢ 
 */
    
    val A11f9a = App(App(Var("f9", i -> (i -> i)), Var("V20",i)), new Var("V3", i))
    val A11p15desiredA = Atom("p15",List(A11f9a))
    val A11f9b = App(App(Var("f9", i -> (i -> i)), Var("V18",i)), new Var("V19", i))
    val A11p15desiredB = Atom("p15",List(A11f9b))    
      val desiredA11d = A11p15desiredB +: Sequent(A11p15desiredA)(Atom("p25",List(Var("V20",i))))
                            
    val rightA11d   = Axiom(Sequent(Atom("p20",List(Var("c15",i))))())
                                
    val leftA11d   = Axiom(A11p15desiredA +: Sequent(A11p15desiredB)(Atom("p20",List(Var("V22",i))),Atom("p25",List(Var("V20",i)))))

    val varsA11d    = MSet[Var](Var("V3",i),Var("V20",i),Var("V18",i),Var("V19",i),Var("V22",i))
    println("L: " + leftA11d)
    println("R: " + rightA11d)
        println("Initial desired: " + desiredA11d)

   //10 Oct: this next one fails
        
    val  URA11d = UnifyingResolution(leftA11d, rightA11d, desiredA11d)(varsA11d)
    println("URd: " + URA11d) 
    
  ///////August 11 2016 Tests End  
  
        /*
     * 10 October 2016
     * 
Left:    (p3 U V) ⊢ (p3 (f4 (f6 X (f7 U NEW1))) V) This is 84 and correct
Left clean: (p3 NEW4 NEW3) ⊢ (p3 (f4 (f6 X (f7 NEW4 NEW1))) NEW3)
Right:  (p3 U W), (p3 U V)  ⊢ (p3 W V) This is 17
Computed : (p3 NEW4 W), (p3 (f4 (f6 X (f7 NEW4 NEW1))) V) ⊢ (p3 W V)
Computed clean: (p3 (f4 (f6 NEW3 (f7 NEW4 NEW1))) NEW2), (p3 NEW4 NEW0) ⊢ (p3 NEW0 NEW2)
Desired: (p3 (f4 (f6 W (f7 U    X   ))) Y),  (p3 U    V)  ⊢ (p3 Y V)   

The desired in this situation is false (requires V in computed to go to V and Y in desired
     * 
     */
    
    
    val O10u = new Var("U",i)
    val O10v = new Var("V",i)
    val O10w = new Var("W",i)
    val O10x = new Var("X",i)
    val O10y = new Var("Y",i)
    val O10new4 = new Var("NEW4",i)
    val O10new3 = new Var("NEW3",i)
    val O10new2 = new Var("NEW2",i)
    val O10new1 = new Var("NEW1",i)
    val O10new0 = new Var("NEW0",i)
    
    val O10leftAnt = Atom("p3",List(O10u,O10v)) 
    val O10LSa = Atom("f4",List(  Atom("f6", List(O10x, Atom("f7", List(O10u, O10new1))      )) )) 
    val O10leftSuc = Atom("p3",List(O10LSa,O10v)) 
    val O10left = Sequent(O10leftAnt)(O10leftSuc)    
    println("l: " + O10left)
    
    val O10rightAnta = Atom("p3",List(O10u,O10w)) 
    val O10rightAntb = Atom("p3",List(O10u,O10v)) 
    val O10rightSuc = Atom("p3",List(O10w,O10v)) 
    val O10right = O10rightAntb +: (Sequent(O10rightAnta)(O10rightSuc))
    println("r: " + O10right)        
    
    val O10desiredAnta = Atom("p3",List(O10u,O10v)) 
    val O10Da = Atom("f4",List(  Atom("f6", List(O10w, Atom("f7", List(O10u, O10x))      )) )) 
    val O10desiredAntb = Atom("p3",List(O10Da,O10y)) 
    val O10desiredSuc = Atom("p3",List(O10y,O10v)) 
    val O10desired = O10desiredAnta +: (Sequent(O10desiredAntb)(O10desiredSuc))
    println("d: " + O10desired)
    
    //Computed : (p3 NEW4 W), (p3 (f4 (f6 X (f7 NEW4 NEW1))) V) ⊢ (p3 W V)
    val O10computedAnta = Atom("p3",List(O10new4,O10w)) 
    val O10Ca = Atom("f4",List(  Atom("f6", List(O10x, Atom("f7", List(O10new4, O10new1))      )) )) 
    val O10computedAntb = Atom("p3",List(O10Ca,O10y))     
    val O10computedSuc = Atom("p3",List(O10w,O10v))
    val O10computed = O10computedAntb +: (Sequent(O10computedAnta)(O10computedSuc))
    println("c: " + O10computed)
    
    //Computed Clean : (p3 (f4 (f6 NEW3 (f7 NEW4 NEW1))) NEW2), (p3 NEW4 NEW0) ⊢ (p3 NEW0 NEW2)
    val O10computedCleanAnta = Atom("p3",List(O10new4,O10new0)) 
    val O10CCleana = Atom("f4",List(  Atom("f6", List(O10new3, Atom("f7", List(O10new4, O10new1))      )) )) 
    val O10computedCleanAntb = Atom("p3",List(O10CCleana,O10new2))     
    val O10computedCleanSuc = Atom("p3",List(O10new0,O10new2))
    val O10computedClean = O10computedCleanAntb +: (Sequent(O10computedCleanAnta)(O10computedCleanSuc))
    println("cClean: " + O10computedClean)    
    
    var O10vars = MSet[Var]()

    O10vars += O10u
    O10vars += O10v
    O10vars += O10w
    O10vars += O10x
    O10vars += O10y
    O10vars += O10new4
    O10vars += O10new3
    O10vars += O10new2
    O10vars += O10new1
    O10vars += O10new0
    
    //Should all be null
    println("Vars: " + O10vars)
    val O10result = findRenaming(O10desired, O10computed)(O10vars)
    println("Result: " + O10result)
    
    val O10resultb = findRenaming(O10computed,O10desired)(O10vars)
    println("ResultB: " + O10resultb)    
    
    val O10resultClean = findRenaming(O10desired, O10computedClean)(O10vars)
    println("ResultC: " + O10resultClean)
    
   // 10 October 2016 tests end
    
    
  println("OUTPUT OF INTEREST -------------")
//  println("7a: " + findSeqTest7A)
//  println("7b: " + findSeqTest7B)
//  val out = tester.findRenaming(findSeqTest7A, findSeqTest7B)(usedVars)
//  println("out: " + out)
  println(leftNodeD)
  println(rightNodeD)
  println(desiredE)
  println("^^^^^^^^^^^^^^^^^^^^^")

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
      URur.asInstanceOf[UnifyingResolution].leftPremise must beEqualTo(URleftNode)
    }
    "return the correct rightPremise" in {
      URur.asInstanceOf[UnifyingResolution].rightPremise must beEqualTo(URrightNode)
    }
    "return the correct clean left (no shared)" in {
      URurB.asInstanceOf[UnifyingResolution].leftClean must beEqualTo(URleftNodeB)
    }
    "return the correct clean left (shared)" in {
      findRenaming(URurC.asInstanceOf[UnifyingResolution].leftClean.conclusion, URleftNodeC.conclusion)(usedVars) != null must beEqualTo(true)
    }
    "return the correct auxL" in {
      findRenaming(Sequent()(URur.asInstanceOf[UnifyingResolution].auxL), Sequent()(App(Var("q", i -> i), a)))(usedVars) != null must beEqualTo(true)
    }
    "return the correct auxR" in {
      findRenaming(Sequent()(URur.asInstanceOf[UnifyingResolution].auxR), Sequent()(App(Var("q", i -> i), y)))(usedVars) != null must beEqualTo(true)
    }
    "return the correct leftAuxFormulas" in {
      findRenaming(URur.asInstanceOf[UnifyingResolution].leftAuxFormulas, Sequent()(App(Var("q", i -> i), a)))(usedVars) != null must beEqualTo(true)
    }
    "return the correct rightAuxFormulas" in {
      findRenaming(URur.asInstanceOf[UnifyingResolution].rightAuxFormulas, Sequent(App(Var("q", i -> i), y))())(usedVars) != null must beEqualTo(true)
    }
    "return the correct mgu" in {
      URur.asInstanceOf[UnifyingResolution].mgu must beEqualTo(Substitution((x, a)))
    }
    "return the correct conclusion context" in {
      findRenaming(URur.conclusionContext, Sequent(App(Var("p", i -> i), y))())(usedVars) != null must beEqualTo(true)
    }
    
    //August 11 2016 Tests
    "Find the desired sequent (general test)" in {
      findRenaming(URA11a.conclusion, desiredA11a)(varsa) != null must beEqualTo(true)
    }
    "Find the desired sequent (checks if invalidMap function uses appropriate variables)" in {
      findRenaming(URA11b.conclusion, desiredA11b)(varsb) != null must beEqualTo(true)
    }
    "Find the desired sequent (checks if containmentOnly flag is set properly (1))" in {
      findRenaming(URA11c.conclusion, desiredA11c)(varsA11c) != null must beEqualTo(true)
    }     
    "Find the desired sequent (checks if containmentOnly flag is set properly (2))" in {
      findRenaming(URA11d.conclusion, desiredA11d)(varsA11d) != null must beEqualTo(true)
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

    // --- formerly checkHalf tests
    "check that a unification is not applied for a sequent half (2 specific vars)" in {
      tester.findRenaming(findSeqTest1A.suc, findSeqTest1B.suc)(usedVars) != null must beEqualTo(false)
    }
    "check that a unification is not applied for a sequent half (1 specific var)" in {
      tester.findRenaming(findSeqTest2A.suc, findSeqTest2B.suc)(usedVars) != null must beEqualTo(false)
    }
    "check that they're equal mod renaming for a sequent half(1 specific var)" in {
      tester.findRenaming(findSeqTest3A.suc, findSeqTest3B.suc)(usedVars) != null must beEqualTo(true)
    }
    "check that they're equal mod renaming for a sequent half (2 universal vars)" in {
      tester.findRenaming(findSeqTest4A.suc, findSeqTest4B.suc)(usedVars) != null must beEqualTo(true)
    }
    "check that they're equal mod renaming for a sequent half (different length)" in {
      tester.findRenaming(findSeqTest5A.ant, findSeqTest5B.ant)(usedVars) != null must beEqualTo(false)
    }
    "check that they're equal mod renaming for a sequent half (different distribution of formulas)" in {
      tester.findRenaming(findSeqTest6A.ant, findSeqTest6B.ant)(usedVars) != null must beEqualTo(false)
    }
    // ---

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

    //----formerly checkHelperAlphaManual tests
    "findRenaming should return the correct result (x->y; true)" in {
      tester.findRenaming(chSeq1A, chSeq1B)(usedVars) != null must beEqualTo(true)
    }
    "findRenaming should return the correct result (x->c; false)" in {
      tester.findRenaming(chSeq2A, chSeq2B)(usedVars) != null must beEqualTo(false)
    }
    "findRenaming should return the correct result (even distribution)" in {
      tester.findRenaming(chSeq4A, chSeq4B)(usedVars) != null must beEqualTo(true)
    }
    "findRenaming should return the correct result (longer desired)" in {
      tester.findRenaming(chSeq5A, chSeq5B)(usedVars) != null must beEqualTo(false)
    }
    "findRenaming should return the correct result (longer computed)" in {
      tester.findRenaming(chSeq6A, chSeq6B)(usedVars) != null must beEqualTo(false)
    }
    "findRenaming should return the correct result (number in desired; longer)" in {
      tester.findRenaming(chSeq7A, chSeq7B)(usedVars) != null must beEqualTo(false)
    }
    //----
    
    //10 Oct 2016
    "findRenaming should not require a variable to mapped to two targets " in {
      tester.findRenaming(O10desired, O10computed)(O10vars) == null must beEqualTo(true)
    }    
    "findRenaming should not require a variable to mapped to two targets (reversed arguments) " in {
      tester.findRenaming(O10computed,O10desired)(O10vars) == null must beEqualTo(true)
    } 
    "findRenaming should not require a variable to mapped to two targets (no shared variables)" in {
      tester.findRenaming(O10desired, O10computedClean)(usedVars) == null must beEqualTo(true)
    }     

    //July 28 tests
    "find the correct sequent in unifying resolution (1)" in {
      ur1.conclusion.equals(ac1) must beEqualTo(true)
    }
    "find the correct sequent in unifying resolution (2)" in {
      ur2.conclusion.equals(ac2) must beEqualTo(true)
    }
    "find the correct sequent in unifying resolution (3)" in {
      ur3.conclusion.equals(ac3) must beEqualTo(true)
    }
    "find the correct sequent in unifying resolution (4)" in {
      ur4.conclusion.equals(ac4) must beEqualTo(true)
    }
    //----
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