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
  usedVars += a

  //p(X) |- q(a)     with    q(X) |- 
  val leftSeq = Sequent(App(Var("p", i -> i), x))(App(Var("q", i -> i), a))
  val rightSeq = Sequent(App(Var("q", i -> i), x))()

  val leftNode = new Axiom(leftSeq)
  val rightNode = new Axiom(rightSeq)

  val ur = UnifyingResolution(leftNode, rightNode)(usedVars)

  "UnifyingResolution" should {
    "return the correct resolvent when necessary to make a substitution" in {
    	//TODO: update this when "SomeNewName" is changed.
      Sequent(App(Var("p", i -> i), Var("SomeNewName", i)))() must beEqualTo(ur.conclusion)
    } //TODO: add test when substitution is not necessary
  }
}