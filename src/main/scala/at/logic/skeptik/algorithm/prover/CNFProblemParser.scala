package at.logic.skeptik.algorithm.prover

import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.parser.TPTPParsers.{CNFAxiomStatement, CNFNegatedConjectureStatement, ProblemParserCNFTPTP}

/**
  * @author Daniyar Itegulov
  */
object CNFProblemParser extends ProblemParser {
  override def parse(filename: String): CNF = {
    val problem = ProblemParserCNFTPTP.problem(filename)
    val clauses = problem.statements.map {
      case axiom: CNFAxiomStatement => new SeqSequent(axiom.ant, axiom.suc)
      case negConj: CNFNegatedConjectureStatement => new SeqSequent(negConj.ant, negConj.suc)
    }
    new CNF(clauses)
  }
}
