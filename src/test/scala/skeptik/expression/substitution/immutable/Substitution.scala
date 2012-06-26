package skeptik.expression
package substitution.immutable

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestsForImmutableSubstitution extends SpecificationWithJUnit {

  val s = Substitution(Var("a",i) -> Var("b", o))
  
  "Substitution" should {
    "return a new collection of type Substitution after a new element is added" in {

      val z = s + (Var("c",i) -> Var("d", o))
      z.getClass.getSimpleName must beEqualTo( s.getClass.getSimpleName )
    }
    "return a new collection of type Substitution after many new elements are added" in {

      val z = s ++ Seq( (Var("c",i) -> Var("d", o)) , (Var("e",i) -> Var("f", o)) )
      z.getClass.getSimpleName must beEqualTo( s.getClass.getSimpleName )
    }
    "return a new collection of type Substitution after map" in {

      val z = s map { case (a,b) => (a,Var("n",i)) }
      z.getClass.getSimpleName must beEqualTo( s.getClass.getSimpleName )
    }
    "return a new collection of type Map2 after a new element of type Seq is added" in {

      val z = s + (Var("c",i) -> Seq("d"))
      z.getClass.getSimpleName must beEqualTo( "Map2" )
    }
  }
}
