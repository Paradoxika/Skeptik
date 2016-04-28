package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{ HashMap => MMap }
import collection.mutable.{ HashSet => MSet }
import collection.mutable.Set
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{ SequentProofNode => Node }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.resolution._
import at.logic.skeptik.expression.substitution.immutable.Substitution

object ProofParserSPASS extends ProofParser[Node] with SPASSParsers

trait SPASSParsers
  extends JavaTokenParsers with RegexParsers with checkUnifiableVariableName {

  private var count = 1 //the count of the line as given by the SPASS proof
  private var lineCounter = 0 //the actual line number, as in the file

  private val proofMap = new MMap[Int, Node]

  private val vars = Set[Var]()

  private val exprMap = new MMap[String, E] //will map axioms/proven expressions to the location (line number) where they were proven

  private val varMap = new MMap[String, E] //will map variable names to an expression object for that variable

  //returns the actual proof
  def proof: Parser[Proof[Node]] = rep(line) ^^ {
    case list => {
      println("Parsed line " + lineCounter + "; done.")
      val p = Proof(list.last)
      lineCounter = 0
      p
    }
  }

  def updateLineCounter = {
    lineCounter += 1

    if (lineCounter % 50 == 0) {
      println("Parsed " + lineCounter + " lines.")
    }
  }

  def newAxiomFromLists(ant: List[E], suc: List[E]): Axiom = {
    val sA = addAntecedents(ant)
    val sS = addSuccedents(suc)
    val sFinal = sA union sS

    new Axiom(sFinal)
  }

  def lowPriority: Parser[List[E]] = "]" ~ rep(formulaList) ~ "||" ^^ {
    case ~(~(_, l), _) => {
      l
    }
  }

  def line: Parser[Node] = number ~ "[" ~ splitNumber ~ ":" ~ inferenceRule ~ repsep(ref, ",") ~ lowPriority ~ sequent ^^ {
    case ~(~(~(~(~(~(~(ln, _), _), _), "Inp"), _), lp), seq) => {
      val ax = newAxiomFromLists(lp ++ seq._1, seq._2)
      proofMap += (ln -> ax)
      updateLineCounter
      ax
    }

    case ~(~(~(~(~(~(~(ln, _), _), _), "Res:"), refs), lp), seq) => {
      def firstRef = refs.head
      def secondRef = refs.tail.head
      def firstNode = firstRef.first
      def secondNode = secondRef.first

      val firstPremise = proofMap.getOrElse(firstNode, throw new Exception("Error!"))
      val secondPremise = proofMap.getOrElse(secondNode, throw new Exception("Error!"))

      val desiredSequent = newAxiomFromLists(lp ++ seq._1, seq._2).conclusion.toSeqSequent

      val ax = try {
        UnifyingResolution(firstPremise, secondPremise, desiredSequent)(vars)
      } catch {
        case e: Exception => {
          e.printStackTrace()
          UnifyingResolution(secondPremise, firstPremise, desiredSequent)(vars)
        }
      }

      val ay = newAxiomFromLists(lp ++ seq._1, seq._2)


      proofMap += (ln -> ax)
      updateLineCounter
      ax
    }
    case ~(~(~(~(~(~(~(ln, _), _), _), "MRR:"), refs), lp), seq) => {
      def firstRef = refs.head
      def secondRef = refs.tail.head
      def firstNode = firstRef.first
      def secondNode = secondRef.first

      val firstPremise = proofMap.getOrElse(firstNode, throw new Exception("Error!"))
      val secondPremise = proofMap.getOrElse(secondNode, throw new Exception("Error!"))

      val desiredSequent = newAxiomFromLists(lp ++ seq._1, seq._2).conclusion.toSeqSequent

      val ax = if (refs.length == 2) {
        try {
          UnifyingResolutionMRR(firstPremise, secondPremise, desiredSequent)(vars)
        } catch {
          case e: Exception => {
            e.printStackTrace()
            UnifyingResolutionMRR(secondPremise, firstPremise, desiredSequent)(vars)
          }
        }
      } else {
        UnifyingResolutionMRR(getAllNodes(refs), desiredSequent)(vars)
      }

      val ay = newAxiomFromLists(lp ++ seq._1, seq._2)
      proofMap += (ln -> ax)
      updateLineCounter
      ax
    }
    case ~(~(~(~(~(~(~(ln, _), _), _), "Con:"), refs), lp), seq) => {
      def firstRef = refs.head
      def firstNode = firstRef.first
      val firstPremise = proofMap.getOrElse(firstNode, throw new Exception("Error!"))

      val desiredSequent = newAxiomFromLists(lp ++ seq._1, seq._2).conclusion.toSeqSequent

      val con = Contraction(firstPremise, desiredSequent)(vars)
      proofMap += (ln -> con)
      updateLineCounter
      con
    }
    //For now, treat the other inference rules as new axioms
    case ~(~(~(~(~(~(~(ln, _), _), _), _), refs), lp), seq) => {
      val ax = newAxiomFromLists(lp ++ seq._1, seq._2)
      proofMap += (ln -> ax)
      ax
    }
  }

  def getAllNodes(r: List[Ref]): List[Node] = {
    if (r.length == 0) {
      List[Node]()
    } else {
      val premise = proofMap.getOrElse(r.head.first, throw new Exception("Error!"))
      List[Node](premise) ++ getAllNodes(r.tail)
    }
  }

  def sequent: Parser[(List[E], List[E])] = antecedent ~ "->" ~ succedent ~ "." ^^ {
    case ~(~(~(a, _), s), _) => {

      //This function maintains a map of the form ((proof line, clause position) -> clause).       
      def addToExprMap(lineNumber: Int, startPos: Int, exps: List[E]): Int = {
        if (exps.length > 1) {
          exprMap.getOrElseUpdate(lineNumber + "." + startPos, exps.head)
          addToExprMap(lineNumber, startPos + 1, exps.tail)
        } else if (exps.length == 1) {
          exprMap.getOrElseUpdate(lineNumber + "." + startPos, exps.head)
          startPos + 1
        } else {
          startPos
        }
      }

      addToExprMap(count, addToExprMap(count, 0, a), s)

      (a, s)
    }
  }

  def antecedent: Parser[List[E]] = rep(formulaList)
  def succedent: Parser[List[E]] = rep(formulaList)

  //All the additional symbols can be ignored, but still must be parsed----
  def formulaList: Parser[E] = (termType1 | maximalTerm | termType2 | term)
  def termType1: Parser[E] = term ~ "*+" ^^ {
    case ~(t, _) => t
  }
  def maximalTerm: Parser[E] = term ~ "*" ^^ {
    case ~(t, _) => t
  }
  def termType2: Parser[E] = term ~ "+" ^^ {
    case ~(t, _) => t
  }
  //---------------------------------------------

  def ref: Parser[Ref] = number ~ "." ~ number ^^ {
    case ~(~(a, _), b) => {
      new Ref(a, b)
    }
  }

  def lineType: Parser[Int] = number ~ ":" ~ inferenceRule ^^ {
    case ~(~(n, _), _) => n
  }

  def inferenceRule: Parser[String] = "Inp" | "Res:" | "Con:" | "MRR:" | otherInferenceRule

  //Other inference rules are currently treated as axioms when parsed.
  //Must be 3 letters with an optional ":"
  def otherInferenceRule: Parser[String] = "[a-zA-Z]{3}:*".r ^^ {
    case s => {
      throw new ParserException("Unsupported rule used; aborting.")
      s
    }
  }

  def func: Parser[E] = name ~ "(" ~ repsep(term, ",") ~ ")" ^^ {
    case ~(~(~(name, _), args), _) => {
      val arrow = getArrow(args)
      AppRec(new Var(name, arrow), args)
    }
  }

  def getArrow(args: List[E]): Arrow = {
    if (args.length > 1) {
      i -> (getArrow(args.tail))
    } else if (args.length == 1) {
      (i -> i)
    } else {
      throw new ParserException("Arrow creation failed")
    }
  }

  def num: Parser[E] = """\d+""".r ^^ {
    case a => {
      new Var(a, i)
    }
  }

  def number: Parser[Int] = """\d+""".r ^^ { _.toInt }

  def splitNumber: Parser[Int] = """\d+""".r ^^ {
    case s: String => {
      val out = s.toInt
      if (out > 0) {
        throw new ParserException("Splitting not supported!")
      }
      out
    }
  }

  def term: Parser[E] = (func | num | variable)

  def variable: Parser[E] = name ^^ {
    case s => {
      varMap.getOrElseUpdate(s, updateVars(s))
    }
  }

  def updateVars(s: String) = {
    val hasLowerCaseFirst = s.charAt(0).isLower
    val v = new Var(s.toString, i)
    if (isValidName(v)) {
      vars += v
    }
    v
  }

  def name: Parser[String] = "[a-zA-Z0-9_]+".r ^^ {
    case s => {
      s
    }
  }

  def addAntecedents(antes: List[E]): Sequent = {
    if (antes.length > 1) {
      val s1 = antes.head +: addAntecedents(antes.tail)
      s1
    } else if (antes.length == 1) {
      val s0 = Sequent()()
      val s1 = antes.head +: s0
      s1
    } else {
      val s0 = Sequent()()
      s0
    }
  }

  def addSuccedents(succs: List[E]): Sequent = {
    if (succs.length > 1) {
      val s1 = addSuccedents(succs.tail) + succs.head
      s1
    } else if (succs.length == 1) {
      val s0 = Sequent()()
      val s1 = s0 + succs.head
      s1
    } else {
      val s0 = Sequent()()
      s0
    }
  }

}

case class ParserException(error: String) extends Exception

class Ref(f: Int, s: Int) {
  def first = f
  def second = s
  override def toString = "(" + f + ", " + s + ")"
}
