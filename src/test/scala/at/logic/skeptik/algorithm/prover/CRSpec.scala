package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.expression._
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

/**
  * @author Daniyar Itegulov
  */
@RunWith(classOf[JUnitRunner])
class CRSpec extends SpecificationWithJUnit {
  val x = Var("x", i)
  val a = Var("a", i)
  val P = Var("P", i -> o)
  val f = Var("f", i -> i)
  implicit val vars = mutable.Set(x)

  private def test(clauses: Clause*) = CR.isSatisfiable(new CNF(ArrayBuffer(clauses:_*)))

  "CR" should {
    "find satisfiable" in {
      test(
        Clause()(App(P, x)),
        Clause()(App(P, a))
      ) shouldEqual true
    }

    "find unsatisfiable" in {
      test(
        Clause(App(P, a))(), // P(a)
        Clause()(App(P, x), App(P, App(f, x))), // ∀x.(P(x) or P(f(x))
        Clause(App(P, App(f, App(f, a))))() // P(f(f(a)))
      ) shouldEqual false
    }
  }
}
