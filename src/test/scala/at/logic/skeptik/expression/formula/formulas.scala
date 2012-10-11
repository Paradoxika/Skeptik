package at.logic.skeptik.expression
package formula

import at.logic.skeptik.expression.position.{PredicatePosition, IndexedPosition}

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class FormulaSpecification extends SpecificationWithJUnit {

  val a = Var("a",i)
  val x = Var("x",i)
  val e = App(
                  App(
                      Var("f", i -> (i -> o)), 
                      a), 
                  a.copy)
  
  "Constructor for universally quantified formula" should {
    "replace all matching terms by the quantified variable" in {

      val q = All(e, x, a.copy)
      q must beEqualTo( App(allC(i), Abs(x.copy, App(App(Var("f", i -> (i -> o)), x.copy), x.copy)))   )
    }

    "replace the term specificied by the given position by the quantified variable" in {

      val q = All(e, x, new PredicatePosition(_ eq a))
      q must beEqualTo( App(allC(i), Abs(x.copy, App(App(Var("f", i -> (i -> o)), x.copy), a.copy)))   )
    }
    
    "replace the term specificied by the given position by the quantified variable" in {

      val q = All(e, x, new IndexedPosition(new PredicatePosition(_ == a), 0))
      q must beEqualTo( App(allC(i), Abs(x.copy, App(App(Var("f", i -> (i -> o)), x.copy), a.copy)))   )
    }
    
    "replace the term specificied by the given position by the quantified variable" in {

      val q = All(e, x, new IndexedPosition(new PredicatePosition(_ == a), 1))
      q must beEqualTo( App(allC(i), Abs(x.copy, App(App(Var("f", i -> (i -> o)), a.copy), x.copy)))   )
    }
  }
  "Unary package method for negation" should {
 
    "construct negated formula correctly" in {
      val q = ¬(e)
      q must beEqualTo( Neg(e) )
    }
  }
}
