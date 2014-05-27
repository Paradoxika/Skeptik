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
class UnifyingResolutionSpecification extends SpecificationWithJUnit {

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
  val leftSeqC =  Sequent()(App(App(Var("le", i -> (i -> o)), b), b))
  var u = new Var("U", i)
  var v = new Var("V", i)
  var w = new Var("W", i)
  val rightSeqC = Sequent( App(App(Var("le", i -> (i -> o)), AppRec(new Var("max", i -> (i -> i)), List(u, v))), w))(App(App(Var("le", i -> (i -> o)), v), w))
  usedVars += u
  usedVars += v
  usedVars += w
  
  val leftNodeC = new Axiom(leftSeqC)
  val rightNodeC = new Axiom(rightSeqC)
  val urC= UnifyingResolution(leftNodeC, rightNodeC)(usedVars)
  
  "UnifyingResolution" should {
    "return the correct resolvent when necessary to make a substitution" in {
//     println("ur: " + ur.conclusion)
      Sequent(App(Var("p", i -> i), Var("NEW0", i)))() must beEqualTo(ur.conclusion)
    } 
    "return the correct resolvent when no substituion necessary" in {
//     println("urB: " + urB.conclusion)
      Sequent(App(Var("p", i -> i),x))() must beEqualTo(urB.conclusion)
    }
    "return the correct resolvent taken from the example" in {
     println("urC: " + urC.conclusion)
      Sequent()(App(App(Var("le", i -> (i -> o)), u), AppRec(new Var("max", i -> (i -> i)), List(v, u)))) must beEqualTo(urC.conclusion)
    }
  }
}