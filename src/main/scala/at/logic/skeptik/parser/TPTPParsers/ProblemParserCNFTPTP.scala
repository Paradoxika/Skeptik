package at.logic.skeptik.parser.TPTPParsers

import at.logic.skeptik.parser.BaseParserTPTP

/**
  * @author  Ezequiel Postan
  * @since   24.05.2016
  * @version 1.0
  * @note    This version accepts only CNF formulas that are taken as axioms
  *          except for a conjeture or negated conjeture. No derivation nodes
  *          or other TPTP annotated formulas are accepted.
  */
object ProblemParserCNFTPTP extends ProblemParserCNFTPTP

/**
  * The ProblemParserFOFTPTP trait implements a parser for problems written
  * in the TPTP CNF syntax. We assume that there are no derivation nodes in
  * the parsed file, i.e. that we only have our axioms and a final conjecture.
  *
  * TODO: Add (if needed) the treatment for FOF formulas and skolemnization steps
  */
trait ProblemParserCNFTPTP
  extends BaseParserTPTP {
}