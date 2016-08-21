package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.expression.{Var, i}
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.parser.TPTPParsers.{CNFAxiomStatement, CNFNegatedConjectureStatement, CNFProblem, ProblemParserCNFTPTP}

import scala.collection.mutable

/**
  * Created by itegulov on 22.07.16.
  */
object CRTest extends App {

  def problemToClauses(problem: CNFProblem): Seq[Clause] = {
    problem.statements.map {
      case axiom: CNFAxiomStatement => new SeqSequent(axiom.ant, axiom.suc)
      case negConj: CNFNegatedConjectureStatement => new SeqSequent(negConj.ant, negConj.suc)
    }
  }

  def time[A](a: => A): Long = {
    val now = System.nanoTime
    val result = a
    (System.nanoTime - now) / 1000
  }

  def test(testName: String)(implicit vars: mutable.Set[Var]) {
    val clauses = problemToClauses(ProblemParserCNFTPTP.problem(s"examples/problems/CNF/$testName.cnfp"))
    val t = time(CR.prove(new CNF(clauses)))
    println(s"Computed $testName in $t microseconds")
  }

  {
    implicit val variables = mutable.Set(Var("V_x", i), Var("V_U", i), Var("T", i), Var("T_a", i))
    test("ANA013-2")
  }

  {
    implicit val variables = mutable.Set(Var("X", i), Var("Y", i), Var("Z", i))
    test("ALG002-1")
  }

  {
    implicit val variables = mutable.Set(Var("X1", i), Var("X2", i), Var("X3", i))
    test("KRS001-1")
  }

  {
    implicit val variables = mutable.Set(Var("X", i), Var("Y", i), Var("Z", i),
      Var("V", i), Var("U", i), Var("W", i), Var("A", i), Var("B", i),
      Var("C", i), Var("D", i))
    test("FLD010-3")
  }

  // Bloats too fast -- need some time to finish
//  {
//    val clauses = problemToClauses(ProblemParserCNFTPTP.problem("examples/problems/CNF/LCL031-1.cnfp"))
//    implicit val variables = mutable.Set(Var("X", i), Var("Y", i), Var("Z", i))
//    println(CR.prove(new CNF(clauses)))
//  }

  {
    implicit val variables = mutable.Set(Var("A", i), Var("B", i), Var("C", i),
      Var("D", i), Var("E", i), Var("F", i),
      Var("G", i), Var("H", i), Var("I", i))
    test("MGT017-1")
  }

  {
    implicit val variables = mutable.Set(Var("A", i), Var("B", i),
      Var("X", i), Var("Y", i), Var("Z", i))
    test("NUM019-1")
  }

  {
    implicit val variables = mutable.Set(Var("A", i), Var("B", i),
      Var("X", i), Var("Y", i), Var("Z", i))
    test("PUZ008-2")
  }

  {
    implicit val variables = mutable.Set(Var("Subset", i), Var("Superset", i),
      Var("Element", i), Var("Set1", i), Var("Set2", i), Var("Intersection", i))
    test("SET006-1")
  }

  {
    implicit val variables = mutable.Set(Var("X", i), Var("Y", i), Var("Z", i))
    test("ANA002-4")
  }

  {
    implicit val variables = mutable.Set(Var("X", i), Var("Y", i), Var("Z", i),
      Var("V", i), Var("U", i), Var("W", i), Var("A", i), Var("B", i),
      Var("C", i), Var("D", i))
    test("FLD041-3")
  }
}
