package skeptik.expression
package substitution.mutable

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestsForMutableSubstitution extends SpecificationWithJUnit {

  val s = Substitution(Var("a",i) -> Var("b", o))
  
  "Substitution" should {
    "remain a collection of type Substitution after a new element is added" in {

      val name = s.getClass.getSimpleName 
      s += (Var("c",i) -> Var("d", o))
      s.getClass.getSimpleName must beEqualTo( name )
    }
    "remain a collection of type Substitution after many new elements are added" in {
      val name = s.getClass.getSimpleName
      s ++= Seq( (Var("c",i) -> Var("d", o)) , (Var("e",i) -> Var("f", o)) )
      s.getClass.getSimpleName must beEqualTo( name )
    }
    "return a new collection of type Substitution after map" in {

      val z = s map { case (a,b) => (a,Var("n",i)) }
      z.getClass.getSimpleName must beEqualTo( s.getClass.getSimpleName )
    }
  }
}
