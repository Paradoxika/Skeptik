package at.logic.skeptik.parser.TPTPParsers

import at.logic.skeptik.expression.{E, Var}
import at.logic.skeptik.parser.BaseParserTPTP
import at.logic.skeptik.parser.TPTPParsers.TPTPAST.{AnnotatedFormula, SimpleFormula, TPTPDirective}

import collection.mutable.Set

/**
  * Created by eze on 2016.07.06..
  */
object ProblemParserTHFTPTP extends ProblemParserTHFTPTP


/**
  * The ProblemParserTHFTPTP trait implements a parser for problems written
  * in the TPTP THF syntax. We assume that there are no derivation nodes in
  * the parsed file, i.e. that we only have our axioms and conjectures.
  */
trait ProblemParserTHFTPTP
  extends BaseParserTPTP {

  def problemParser : Parser[THFProblem] = TPTP_file ^^ generateProblem

  def generateProblem(directives : List[TPTPDirective]) : THFProblem = {
    val onlyFormulas : List[TPTPDirective]       = directives filter isSimpleFormula
    val formulas   : List[(String,String,E)]     = onlyFormulas map extractFormulas
    val statements : List[THFProblemStatement]   = formulas map ((t : (String,String,E)) => formulaToStatement(t._1,t._2,t._3))
    THFProblem(statements,getSeenVars)
  }

  def isSimpleFormula(directive: TPTPDirective) : Boolean = directive match {
    case AnnotatedFormula(language,name,role,SimpleFormula(formula),_) if language == lexical.THF.chars => true
    case _                                                                                              => false
  }

  def extractFormulas(directive : TPTPDirective) : (String,String,E) =
    directive match {
      case AnnotatedFormula(language,name,role,SimpleFormula(formula),_) if language == lexical.THF.chars => (name,role,formula)
      case _                                                                                              => throw new Exception("Unexpected Format")
    }

  def formulaToStatement(name : String, role : String, formula : E) : THFProblemStatement =
    role match {
      case "conjecture"         => THFConjectureStatement(name,formula)
      case "negated_conjecture" => THFNegatedConjectureStatement(name,formula)
      case _                    => THFAxiomStatement(name,formula)
    }


  def problem(fileName : String) : THFProblem = extract(fileName,problemParser)

}

class THFProblem(val statements : List[THFProblemStatement], val variables : Set[Var]) {
  override def toString : String = statements.mkString("\n") + "\nVariables: " + variables.mkString(",")
}
object THFProblem {
  def apply(statements: List[THFProblemStatement],variables : Set[Var]): THFProblem = new THFProblem(statements,variables)
}

abstract class THFProblemStatement
case class THFAxiomStatement(name : String, formula : E) extends THFProblemStatement {
  override def toString : String = "thf("+name + ",axiom," + formula.toString + ")"
}
case class THFConjectureStatement(name : String, formula : E) extends THFProblemStatement {
  override def toString : String = "thf("+name + ",conjecture," + formula.toString + ")"
}
case class THFNegatedConjectureStatement(name : String, formula : E) extends THFProblemStatement {
  override def toString : String = "thf("+name + ",negated_conjecture," + formula.toString + ")"
}

