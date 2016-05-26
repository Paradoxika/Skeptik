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

  def reset() { nodeMap.clear() }

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
      case None             => annotatedFormulaToAxiom(annotatedFormula)
      case Some((source,_)) => annotatedFormulaToNode(annotatedFormula,source)
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

  private def annotatedFormulaToNode(annotatedFormula : AnnotatedFormula, source: Source) : Node = {
    val sourceInfo      = source.term
    val inferenceRecord = sourceInfo.filter(getData(_).nonEmpty)
    if(isAnAxion(inferenceRecord)) annotatedFormulaToAxiom(annotatedFormula)
    else {
      require(inferenceRecord.length == 1)
      val List(rule,_,parentList) = getData(inferenceRecord.head).get
      val inferenceRule = extractRuleName(rule)
      val parents       = extractParents(parentList)
      ??? // TODO: Complete this. The only thing to do is to compare the inferenceRule with the accepted ones
          //       and call a corresponding ProofNode constructor
    }
  }

  // annotatedFormulaToNode auxiliary functions
  private def getData(term : Either[GeneralData,List[GeneralTerm]]) : Option[List[GeneralTerm]] = term match {
    case Left(GFunc("inference",list)) => Some(list)
    case _                             => None
  }
  private def isAnAxion(records : List[Either[GeneralData,List[GeneralTerm]]]) : Boolean = records.isEmpty
  private def extractRuleName(term : GeneralTerm) : String = term match {
    case GeneralTerm(List(Left(GWord(name)))) => name
    case _                                    => throw new Exception("Unexpercted format for inference rule.\n Found: "+ term.toString)
  }
  private def extractParents(term : GeneralTerm) : List[String] = {
    def formarParent(parent : Either[GeneralData,List[GeneralTerm]]) : String = parent match {
      case Left(GWord(p1)) => p1
      case _              => throw new Exception("Unexpected parent format!\nOnly names are allowd.\nFound: "+ parent.toString)
    }
    term match {
      case GeneralTerm(List(Right(List(GeneralTerm(parentList))))) => parentList map formarParent
      case _                                        => throw new Exception("Unexpercted format for parents. Only parents name are accepted\n Found: "+ term.toString)
    }
  }







  def read(fileName: String) : Proof[Node] = {
    val p : Proof[Node] = parse(fileName,proof) match {
      case Success(p2,_)      => p2
      case Error(message,_)   => throw new Exception("Error: " + message)
      case Failure(message,_) => throw new Exception("Failure: " + message)
    }
    reset()
    p
  }
}

