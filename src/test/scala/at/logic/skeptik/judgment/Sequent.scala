package at.logic.skeptik.judgment

import at.logic.skeptik.expression._
import at.logic.skeptik.util.unicode._

import at.logic.skeptik.expression.position.{PredicatePosition, IndexedPosition}

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestsForSequent extends SpecificationWithJUnit {

  val a = Var("a", o)
  val x = Var("x", o)
  val s = immutable.SeqSequent(a,x)(a,x,a,x)
  
  "Sequent" should {
    "give a nicely formated string when toString is called" in {
      s.toString must beEqualTo( "a, x" + unicodeOrElse(" \u22A2 "," :- ") + "a, x, a, x")
    }
  }
}
