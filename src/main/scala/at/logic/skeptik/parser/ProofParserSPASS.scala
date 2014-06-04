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
  extends JavaTokenParsers with RegexParsers {

  private var count = 1 //the count of the line as given by the SPASS proof
  private var lineCounter = 0 //the actual line number, as in the file

  private var proofMap = new MMap[Int, Node]

  private var vars = Set[Var]() //TODO: make this val

  private var exprMap = new MMap[String, E] //will map axioms/proven expressions to the location (line number) where they were proven

  private var varMap = new MMap[String, E] //will map variable names to an expression object for that variable

  //returns the actual proof
  def proof: Parser[Proof[Node]] = rep(line) ^^ {
    case list => {
      println("Parsed line labelled " + count + "; done.")
      //      println(varMap)
      //      println(exprMap)
      val p = Proof(list.last)
      exprMap = new MMap[String, E]
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

  def line: Parser[Node] = number ~ "[" ~ number ~ ":" ~ inferenceRule ~ repsep(ref, ",") ~ "] ||" ~ sequent ^^ {
    //TODO: needs to change to use unifying resolution & other inference rules
    case ~(~(~(~(~(~(~(ln, _), _), _), "Inp"), _), _), seq) => {
      val sA = addAntecedents(seq._1)

      val sS = addSuccedents(seq._2)

      val sFinal = sA union sS

      val ax = new Axiom(sFinal)
      proofMap += (ln -> ax)
      //      println("line: " + ln + " " + ax)
      updateLineCounter
      ax
    }

    case ~(~(~(~(~(~(~(ln, _), _), _), "Res:"), refs), _), seq) => {
      def firstRef = refs.head
      def secondRef = refs.tail.head
      def firstNode = firstRef.first
      def secondNode = secondRef.first

      def firstFormula = exprMap.getOrElse(firstRef.first + "." + firstRef.second, throw new Exception("Error!"))
      def secondFormula = exprMap.getOrElse(secondRef.first + "." + secondRef.second, throw new Exception("Error!"))

      val firstPremise = proofMap.getOrElse(firstNode, throw new Exception("Error!"))
      val secondPremise = proofMap.getOrElse(secondNode, throw new Exception("Error!"))

      //      println("Attempting to parse line " + ln)
      //            println("First premise: " + firstPremise)
      //            println("First formula: " + firstFormula)
      //            println("Second premise: " + secondPremise)
      //            println("Second formula: " + secondFormula)

      val ax = UnifyingResolution(firstPremise, secondPremise)(vars)

      val parsedAnte = addAntecedents(seq._1)
      val parsedSucc = addSuccedents(seq._2)
      val parsedFinal = parsedAnte union parsedSucc

      val ay = new Axiom(parsedFinal)
      //            println("Parsed: " + ln + ":" + ay)
      //            println("Computed: " + ln + ":" + ax)
      proofMap += (ln -> ax)
      updateLineCounter
      ax
    }
    case ~(~(~(~(~(~(~(ln, _), _), _), "MRR:"), refs), _), seq) => {
      def firstRef = refs.head
      def secondRef = refs.tail.head
      def firstNode = firstRef.first
      def secondNode = secondRef.first

      def firstFormula = exprMap.getOrElse(firstRef.first + "." + firstRef.second, throw new Exception("Error!"))
      def secondFormula = exprMap.getOrElse(secondRef.first + "." + secondRef.second, throw new Exception("Error!"))

      val firstPremise = proofMap.getOrElse(firstNode, throw new Exception("Error!"))
      val secondPremise = proofMap.getOrElse(secondNode, throw new Exception("Error!"))

      var lastPremise = null.asInstanceOf[Node]
      if (firstNode == secondNode) {
        val lastRef = refs.last
        val lastNode = lastRef.first
        lastPremise = proofMap.getOrElse(lastNode, throw new Exception("Error!"))
      }

      //      println("Attempting to parse line " + ln)
      //            println("First premise: " + firstPremise)
      //            println("First formula: " + firstFormula)
      //            println("Second premise: " + secondPremise)
      //            println("Second formula: " + secondFormula)

      var ax = null.asInstanceOf[Node]
      if (firstNode != secondNode) {
        //THIS CHANGED
        ax = UnifyingResolution(firstPremise, secondPremise)(vars)

        var con = Contraction(ax)(vars)
        //        println("UR-MRR: " + ax)
        //        println("UR-CON: " + con)
        while (!con.conclusion.equals(ax.conclusion)) {
          ax = con
          con = Contraction(ax)(vars)
          //          println("UR-CON: " + con)
        }

      } else {
        var axA = UnifyingResolutionMRR(lastPremise, firstPremise)(vars)
        var axB = UnifyingResolutionMRR(lastPremise, secondPremise)(vars)
        //Since all examples so far have the first two premises referencing the same line, I'm doing this:
        if (axA.conclusion.suc.length == 0 && axA.conclusion.suc.length == 0) {
          ax = axA //  UnifyingResolution(axB, axA)(vars) //need something like this?
        } else {
          throw new ParserException("MRR invalid form")
        }
      }

      val parsedAnte = addAntecedents(seq._1)
      val parsedSucc = addSuccedents(seq._2)
      val parsedFinal = parsedAnte union parsedSucc

      val ay = new Axiom(parsedFinal)
      //            println("Parsed MRR: " + ln + ":" + ay)
      //            println("Computed MRR: " + ln + ":" + ax)
      proofMap += (ln -> ax)
      updateLineCounter
      ax
    }
    //For now, treat the other inference rules as new axioms
    case ~(~(~(~(~(~(~(ln, _), _), _), _), refs), _), seq) => {

      val sA = addAntecedents(seq._1)

      val sS = addSuccedents(seq._2)

      val sFinal = sA union sS

      val ax = new Axiom(sFinal)
      proofMap += (ln -> ax)
      ax
    }
  }

  def sequent: Parser[(List[E], List[E])] = antecedent ~ "->" ~ succedent ~ "." ^^ {
    case ~(~(~(a, _), s), _) => {

      //This function maintains a map of the form ((proof line, clause position) -> clause).       
      def addToExprMap(lineNumber: Int, startPos: Int, exps: List[E]): Int = {
        if (exps.length > 1) {
          exprMap.getOrElseUpdate(lineNumber + "." + startPos, exps.head)
          //          println(lineNumber + "." + startPos + " == " + exps.head)
          addToExprMap(lineNumber, startPos + 1, exps.tail)
        } else if (exps.length == 1) {
          exprMap.getOrElseUpdate(lineNumber + "." + startPos, exps.head)
          //          println(lineNumber + "." + startPos + " == " + exps.head)
          startPos + 1
        } else {
          startPos
        }
      }

      addToExprMap(count, addToExprMap(count, 0, a), s)

      updateLineCounter
      (a, s)
    }
  }

  def antecedent: Parser[List[E]] = rep(formulaList)
  def succedent: Parser[List[E]] = rep(formulaList)

  //All the additional symbols can be ignored
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

  def ref: Parser[Ref] = number ~ "." ~ number ^^ {
    case ~(~(a, _), b) => {
      new Ref(a, b)
    }
  }

  def lineType: Parser[Int] = number ~ ":" ~ inferenceRule ^^ {
    case ~(~(n, _), _) => n
  }

  //TODO: get complete list from SPASS documentation
  def inferenceRule: Parser[String] = "Inp" | "Res:" | "Spt:" | "Con:" | "MRR:" | "UnC:"

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

  def term: Parser[E] = (func | num | variable)

  def variable: Parser[E] = name ^^ {
    case s => {
      val hasLowerCase = s.exists(_.isLower)
      if (!hasLowerCase) {
        vars += new Var(s.toString, i)
      }
      varMap.getOrElseUpdate(s, new Var(s.toString, i))
    }
  }

  def name: Parser[String] = "[a-zA-Z0-9]+".r ^^ {
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
