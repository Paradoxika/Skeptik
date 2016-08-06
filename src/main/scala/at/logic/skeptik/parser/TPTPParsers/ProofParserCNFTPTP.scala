package at.logic.skeptik.parser.TPTPParsers

import at.logic.skeptik.expression.Var
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.parser.{BaseParserTPTP, ProofParser}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.resolution.{Contraction, UnifyingResolution}
import at.logic.skeptik.proof.sequent.lk.{Axiom, R, UncheckedInference}

import at.logic.skeptik.parser.TPTPParsers.TPTPAST._
import at.logic.skeptik.parser.UnexpectedEmptyTPTPFileException

import collection.mutable.{HashMap => MMap, HashSet => MSet, Set}


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

  private var nodeMap   = new MMap[String,Node]
  private var variables = Set[Var]()
  def getVariables      = variables.clone()

  def reset() {
    resetVarsSeen()
    nodeMap.clear()
    newNameCoubter = 0
  }

  //Obtain the actual proof
  def proof: Parser[Proof[Node]] = TPTP_file ^^ generateProof

  def read(fileName: String) : Proof[Node] = {
    val p : Proof[Node] = extract(fileName,proof)
    reset()
    p
  }

  ////////////////////////////////////////////////////////////////////
  // Proof generation
  ////////////////////////////////////////////////////////////////////
  private def generateProof(directives : List[TPTPDirective]) : Proof[Node] = {
    val expandedDirectives : List[TPTPDirective] = expandIncludes(directives,TPTP_file)
    if (expandedDirectives.isEmpty) throw new UnexpectedEmptyTPTPFileException
    else {
      variables = getSeenVars
      Proof(expandedDirectives.map(prossesDirective).last)
    }
  }

  private def prossesDirective(directive : TPTPDirective) : Node = {
    val annotatedFormula : AnnotatedFormula = directive.asInstanceOf[AnnotatedFormula]
    require(annotatedFormula.language == lexical.CNF.chars)
    if(annotatedFormula.role == "axiom")
      annotatedFormulaToAxiom(annotatedFormula)
    else {
      annotatedFormula.annotations match {
        case None              => annotatedFormulaToAxiom(annotatedFormula)
        case Some((source, _)) => annotatedFormulaToNode(annotatedFormula, source)
      }
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
      createNode(annotatedFormula.name,Some(annotatedFormula.formula),getData(inferenceRecord.head))
    }
  }

  private def createNode(nodeName : String,formula: Option[RepresentedFormula],recordData: List[GeneralTerm]): Node = {
    val List(rule,_,parentList) = recordData
    val inferenceRule = extractRuleName(rule)
    val parents       = extractParents(parentList)
    inferenceRule match {
      case "sr" => annotatedFormulaToResolution(nodeName,formula,parents)
      case "cn" => annotatedFormulaToContraction(nodeName,formula,parents)
      case _    => throw new Exception("Inference Rule not supported: "+ inferenceRule)
    }
    // TODO: Complete this. The only thing to do is to compare the inferenceRule with the accepted ones
    //       and call a corresponding ProofNode constructor. Use Option[RepresentedFormula] for constructors
    //       because a None case will occur when we have nested inference records.
  }

  // annotatedFormulaToNode auxiliary functions
  private def getData(term : Either[GeneralData,List[GeneralTerm]]) : List[GeneralTerm] = term match {
    case Left(GFunc("inference",list)) => list
    case _                             => Nil
  }
  private def isAnAxion(records : List[Either[GeneralData,List[GeneralTerm]]]) : Boolean = records.isEmpty
  private def extractRuleName(term : GeneralTerm) : String = term match {
    case GeneralTerm(List(Left(GWord(name)))) => name
    case _                                    => throw new Exception("Unexpercted format for inference rule.\n Found: "+ term.toString)
  }

  private var newNameCoubter = 0

  private def extractParents(term : GeneralTerm) : List[String] = {
    def formarParent(parent : GeneralTerm) : String = parent match {
      case GeneralTerm(List(Left(GWord(p1))))               => p1
      case GeneralTerm(List(Left(GNumber(p1))))             => p1
      case GeneralTerm(List(Left(GFunc("inference",list)))) => {
        //This is the case where an inference record is nested inside another
        val newName = "NewNode"+ newNameCoubter.toString
        newNameCoubter += 1
        createNode(newName,None,list)
        newName
      }
      case _              => throw new Exception("Unexpected parent format!\nOnly names are allowd.\nFound: "+ parent.toString)
    }
    term match {
      case GeneralTerm(List(Right(parentList))) => parentList map formarParent
      case _                                    => throw new Exception("Unexpercted format for parents. Only parents name are accepted\n Found: "+ term.toString)
    }
  }

  private def annotatedFormulaToResolution(nodeName : String, formula: Option[RepresentedFormula] , parents : List[String]) : Node = {
    require(parents.length == 2)
    if(formula.isEmpty) {
      val resolution = unify(nodeMap(parents(0)), nodeMap(parents(1)), None ,variables)
      nodeMap += (nodeName -> resolution)
      resolution
    } else {
      val sequent = formula match {
        case Some(SimpleSequent(ant, suc)) => Some(Sequent(ant: _*)(suc: _*))
        case _                             => throw new Exception("Unexpected formula found, a sequent was spected")
      }
      val resolution = unify(nodeMap(parents(0)), nodeMap(parents(1)), sequent, variables)
      nodeMap += (nodeName -> resolution)
      resolution
    }
  }

  private def annotatedFormulaToContraction(nodeName : String, formula: Option[RepresentedFormula] , parents : List[String]) : Node = {
    require(parents.length == 1)
    if (formula.isEmpty) {
      nodeMap += (nodeName -> Contraction(nodeMap(parents(0)))(variables))
      nodeMap(nodeName)
    } else {
      val sequent = formula match {
        case Some(SimpleSequent(ant, suc)) => Sequent(ant: _*)(suc: _*)
        case _                             => throw new Exception("Unexpected formula found, a sequent was spected")
      }
      nodeMap += (nodeName -> Contraction(nodeMap(parents(0)),sequent)(variables))
      nodeMap(nodeName)
    }
  }

  private def unify(left : Node, right: Node, conclussion : Option[Sequent], vars : Set[Var]) = {
    try {
      if(conclussion.isEmpty)
        UnifyingResolution(left,right)(vars)
      else
        UnifyingResolution(left,right,conclussion.get)(vars)
    } catch {
      case e: Exception => {
        if(conclussion.isEmpty)
          UnifyingResolution(left,right)(vars)
        else
          UnifyingResolution(right, left, conclussion.get)(vars)
      }
    }
  }

}