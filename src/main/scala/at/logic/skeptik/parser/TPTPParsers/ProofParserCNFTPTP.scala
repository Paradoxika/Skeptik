package at.logic.skeptik.parser.TPTPParsers

import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.parser.{BaseParserTPTP, ProofParser}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{Axiom, R, UncheckedInference}

import at.logic.skeptik.parser.TPTPParsers.TPTPAST._
import at.logic.skeptik.parser.UnexpectedEmptyTPTPFileException

import collection.mutable.{HashMap => MMap}


/**
  * Created by eze on 2016.05.25..
  */
object ProofParserCNFTPTP extends ProofParser[Node] with ProofParserCNFTPTP

/**
  * The ProofParserCNFTPTP trait implements a parser for the CNF fragment of TPTP syntax.
  * It recognizes only CNF cormulas, with contraction and resolution rules.
  *
  * TODO: Add more rules (if needed)
  *
  */
trait ProofParserCNFTPTP
extends BaseParserTPTP {


  private var nodeMap = new MMap[String,Node]

  def reset() : Unit = {nodeMap.clear()}

  //Obtain the actual proof
  def proof: Parser[Proof[Node]] = TPTP_file ^^ generateProof

  ////////////////////////////////////////////////////////////////////
  // Proof generation
  ////////////////////////////////////////////////////////////////////
  private def generateProof(directives : List[TPTPDirective]) : Proof[Node] = {
    val expandedDirectives : List[TPTPDirective] = expandIncludes(directives,TPTP_file)
    if (expandedDirectives.isEmpty) throw new UnexpectedEmptyTPTPFileException
    else Proof(expandedDirectives.map(prossesDirective).last)
  }

  private def prossesDirective(directive : TPTPDirective) : Node = {
    val annotatedFormula : AnnotatedFormula = directive.asInstanceOf[AnnotatedFormula]
    require(annotatedFormula.language == lexical.CNF.chars)
    annotatedFormula.annotations match {
      case None    => annotatedFormulaToAxiom(annotatedFormula)
      case Some(x) => annotatedFormulaToInference(annotatedFormula)
    }
  }

  private def annotatedFormulaToAxiom(annotatedFormula : AnnotatedFormula) : Node = annotatedFormula.formula match {
    case SimpleSequent(ant,suc) => {
      val axiom = Axiom(Sequent(ant:_*)(suc:_*))
      nodeMap += (annotatedFormula.name -> axiom)
      axiom
    }
    case SimpleFormula(formula) => throw new Exception("Not sequent formula detected: " + annotatedFormula.name)
  }

  private def annotatedFormulaToInference(annotatedFormula : AnnotatedFormula) : Node = ???

  def read(filename: String) : Proof[Node] = {
    val p : Proof[Node] = parse(filename,proof) match {
      case Success(p2,_)      => p2
      case Error(message,_)   => throw new Exception("Error: " + message)
      case Failure(message,_) => throw new Exception("Failure: " + message)
    }
    reset()
    p
  }
}

