package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.expression.{Var, i}
import at.logic.skeptik.judgment.immutable.SetSequent
import at.logic.skeptik.parser.TPTPParsers.{CNFAxiomStatement, CNFNegatedConjectureStatement, ProblemParserCNFTPTP}

import scala.collection.mutable

/**
  * Created by itegulov on 22.07.16.
  */
object CRTest extends App {
  {
    val problem = ProblemParserCNFTPTP.problem("examples/problems/CNF/ANA013-2.cnfp")
    val clauses = problem.statements.map {
      case axiom: CNFAxiomStatement => new SetSequent(axiom.ant.toSet, axiom.suc.toSet)
      case negConj: CNFNegatedConjectureStatement => new SetSequent(negConj.ant.toSet, negConj.suc.toSet)
    }
    implicit val variables = mutable.Set(Var("V_x", i), Var("V_U", i), Var("T", i), Var("T_a", i))
    println(CR.isSatisfiable(new CNF(clauses)))
  }

  {
    val problem = ProblemParserCNFTPTP.problem("examples/problems/CNF/ALG002-1.cnfp")
    val clauses = problem.statements.map {
      case axiom: CNFAxiomStatement => new SetSequent(axiom.ant.toSet, axiom.suc.toSet)
      case negConj: CNFNegatedConjectureStatement => new SetSequent(negConj.ant.toSet, negConj.suc.toSet)
    }
    implicit val variables = mutable.Set(Var("X", i), Var("Y", i), Var("Z", i))
    println(CR.isSatisfiable(new CNF(clauses)))
  }

  {
    val problem = ProblemParserCNFTPTP.problem("examples/problems/CNF/KRS001-1.cnfp")
    val clauses = problem.statements.map {
      case axiom: CNFAxiomStatement => new SetSequent(axiom.ant.toSet, axiom.suc.toSet)
      case negConj: CNFNegatedConjectureStatement => new SetSequent(negConj.ant.toSet, negConj.suc.toSet)
    }
    implicit val variables = mutable.Set(Var("X1", i), Var("X2", i), Var("X3", i))
    println(CR.isSatisfiable(new CNF(clauses)))
  }

  {
    val problem = ProblemParserCNFTPTP.problem("examples/problems/CNF/FLD010-3.cnfp")
    val clauses = problem.statements.map {
      case axiom: CNFAxiomStatement => new SetSequent(axiom.ant.toSet, axiom.suc.toSet)
      case negConj: CNFNegatedConjectureStatement => new SetSequent(negConj.ant.toSet, negConj.suc.toSet)
    }
    implicit val variables = mutable.Set(Var("X", i), Var("Y", i), Var("Z", i),
      Var("V", i), Var("U", i), Var("W", i), Var("A", i), Var("B", i),
      Var("C", i), Var("D", i))
    println(CR.isSatisfiable(new CNF(clauses)))
  }

  {
    val problem = ProblemParserCNFTPTP.problem("examples/problems/CNF/LCL031-1.cnfp")
    val clauses = problem.statements.map {
      case axiom: CNFAxiomStatement => new SetSequent(axiom.ant.toSet, axiom.suc.toSet)
      case negConj: CNFNegatedConjectureStatement => new SetSequent(negConj.ant.toSet, negConj.suc.toSet)
    }
    implicit val variables = mutable.Set(Var("X", i), Var("Y", i), Var("Z", i))
    println(CR.isSatisfiable(new CNF(clauses)))
  }

  {
    val problem = ProblemParserCNFTPTP.problem("examples/problems/CNF/MGT017-1.cnfp")
    val clauses = problem.statements.map {
      case axiom: CNFAxiomStatement => new SetSequent(axiom.ant.toSet, axiom.suc.toSet)
      case negConj: CNFNegatedConjectureStatement => new SetSequent(negConj.ant.toSet, negConj.suc.toSet)
    }
    implicit val variables = mutable.Set(Var("A", i), Var("B", i), Var("C", i),
      Var("D", i), Var("E", i), Var("F", i),
      Var("G", i), Var("H", i), Var("I", i))
    println(CR.isSatisfiable(new CNF(clauses)))
  }
}
