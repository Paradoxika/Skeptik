package at.logic.skeptik.parser.TPTPParsers

import at.logic.skeptik.parser.BaseParserTPTP

/**
  * Created by eze on 2016.05.25..
  */
object ProblemParserFOFTPTP extends ProblemParserFOFTPTP

/**
  * The ProblemParserFOFTPTP trait implements a parser for problems written
  * in the TPTP FOF syntax. We assume that there are no derivation nodes in
  * the parsed file, i.e. that we only have our axioms and conjectures.
  */
trait ProblemParserFOFTPTP
  extends BaseParserTPTP {
}
