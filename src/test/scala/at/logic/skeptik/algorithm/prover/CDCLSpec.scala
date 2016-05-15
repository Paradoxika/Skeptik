package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.expression.{Var, i}
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

import scala.collection.mutable.ArrayBuffer

/**
  * @author Daniyar Itegulov
  */
@RunWith(classOf[JUnitRunner])
class CDCLSpec extends SpecificationWithJUnit {
  private val a = new Var("A", i)
  private val b = new Var("B", i)
  private val c = new Var("C", i)
  private val d = new Var("D", i)
  private val e = new Var("E", i)
  private val f = new Var("F", i)
  private val x = new Var("X", i)
  private val y = new Var("Y", i)
  private val z = new Var("Z", i)

  private def test(clauses: Clause*) = CDCL.isSatisfiable(new Cnf(ArrayBuffer(clauses:_*)))

  "CDCL" should {
    "find satisfiable" in {
      test(
        Clause(a, b)(),
        Clause()(b, c),
        Clause(c)(d),
        Clause()(a)
      ) shouldEqual true

      test(
        Clause(a)(b),
        Clause(b, c)(),
        Clause(d)(c)
      ) shouldEqual true

      test(
        Clause(b)(a, x),
        Clause(c)(a),
        Clause()(b, c, d)
      ) shouldEqual true

      test(
        Clause(b)(a, x),
        Clause(c)(a),
        Clause()(b, c, d),
        Clause(d, e)(),
        Clause(d, f)(y),
        Clause()(e, f)
      ) shouldEqual true
    }

    "find unsatisfiable" in {
      test(
        Clause(a)(),
        Clause()(a)
      ) shouldEqual false
    }
  }
}
