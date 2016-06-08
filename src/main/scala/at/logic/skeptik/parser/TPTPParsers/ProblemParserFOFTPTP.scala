package at.logic.skeptik.parser.TPTPParsers

import at.logic.skeptik.expression.{E, Var}
import at.logic.skeptik.parser.BaseParserTPTP
import at.logic.skeptik.parser.TPTPParsers.TPTPAST.{AnnotatedFormula, SimpleFormula, TPTPDirective}

import collection.mutable.Set
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

  def problemParser : Parser[FOFProblem] = TPTP_file ^^ generateProblem

  def generateProblem(directives : List[TPTPDirective]) : FOFProblem = {
    val expandedDirectives : List[TPTPDirective] = expandIncludes(directives,TPTP_file)
    val formulas   : List[(String,String,E)]     = expandedDirectives map extractFormulas
    val statements : List[FOFProblemStatement]   = formulas map ((t : (String,String,E)) => formulaToStatement(t._1,t._2,t._3))
    FOFProblem(statements,getSeenVars)
  }


  def extractFormulas(directive : TPTPDirective) : (String,String,E) =
    directive match {
      case AnnotatedFormula(language,name,role,SimpleFormula(formula),_) if language == lexical.FOF.chars => (name,role,formula)
      case _                                                                                              => throw new Exception("Unexpected Format")
    }

  def formulaToStatement(name : String, role : String, formula : E) : FOFProblemStatement =
    role match {
      case "conjecture"         => FOFConjectureStatement(name,formula)
      case "negated_conjecture" => FOFNegatedConjectureStatement(name,formula)
      case _                    => FOFAxiomStatement(name,formula)
    }


  def problem(fileName : String) : FOFProblem = extract(fileName,problemParser)

}

class FOFProblem(val statements : List[FOFProblemStatement], val variables : Set[Var]) {
  override def toString : String = statements.mkString("\n") + "\nVariables: " + variables.mkString(",")
}
object FOFProblem {
  def apply(statements: List[FOFProblemStatement],variables : Set[Var]): FOFProblem = new FOFProblem(statements,variables)
}

abstract class FOFProblemStatement
case class FOFAxiomStatement(name : String, formula : E) extends FOFProblemStatement {
  override def toString : String = "fof("+name + ",axiom," + formula.toString + ")"
}
case class FOFConjectureStatement(name : String, formula : E) extends FOFProblemStatement {
  override def toString : String = "fof("+name + ",conjecture," + formula.toString + ")"
}
case class FOFNegatedConjectureStatement(name : String, formula : E) extends FOFProblemStatement {
  override def toString : String = "fof("+name + ",negated_conjecture," + formula.toString + ")"
}