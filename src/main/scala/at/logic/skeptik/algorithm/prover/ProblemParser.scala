package at.logic.skeptik.algorithm.prover

/**
  * @author Daniyar Itegulov
  */
trait ProblemParser {
  def parse(filename: String): CNF
}
