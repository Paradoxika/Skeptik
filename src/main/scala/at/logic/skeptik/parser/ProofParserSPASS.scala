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

  var count = 1; //TODO: make private again; public only for debugging.

  private var proofMap = new MMap[Int, Node]

  private var vars = Set[Var]() //TODO: make this val

  private var exprMap = new MMap[String, E] //will map axioms/proven expressions to the location (line number) where they were proven

  private var varMap = new MMap[String, E] //will map variable names to an expression object for that variable

  //returns the actual proof
  def proof: Parser[Proof[Node]] = rep(line) ^^ {
    case list => {
      println("parsed! " + count)
      //      println(varMap)
      //      println(exprMap)
      val p = Proof(list.last)
      exprMap = new MMap[String, E]
      p
    }
  }

  def line: Parser[Node] = lineNum ~ "[" ~ number ~ ":" ~ inferenceRule ~ rep(lineRef) ~ "] ||" ~ sequent ^^ {
    //TODO: needs to change to use unifying resolution & other inference rules
    case ~(~(~(~(~(~(~(ln, _), _), _), "Inp"), _), _), seq) => {
      val sA = addAntecedents(seq._1)

      val sS = addSuccedents(seq._2)

      val sFinal = sA union sS

      val ax = new Axiom(sFinal)
      proofMap += (ln -> ax)
      println("line: " + ln + " " + ax)
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
      println("Parsed: " + ln + ":" + ay)
      println("Computed: " + ln + ":" + ax)
      proofMap += (ln -> ax)
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

      if (count % 500 == 0) { println(count + " lines parsed") }
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

  def lineNum: Parser[Int] = number ^^ {
    case n => {
      count = n
      n
    }
  }

  def lineRef: Parser[Ref] = (refComma | ref)

  def refComma: Parser[Ref] = ref ~ "," ^^ {
    case ~(r, _) => r
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

  def func: Parser[E] = equals | max | userDef | lessEquals | greaterEquals | max2

  def equals: Parser[E] = "eq(" ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(_, first), _), second), _) => {
      App(App(Var("eq", i -> (i -> o)), first), second)
    }
  }

  def lessEquals: Parser[E] = "le(" ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(_, first), _), second), _) => {
      App(App(Var("le", i -> (i -> o)), first), second)
    }
  }

  def greaterEquals: Parser[E] = "ge(" ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(_, first), _), second), _) => {
      App(App(Var("ge", i -> (i -> o)), first), second)
    }
  }

  def max: Parser[E] = "max(" ~ term ~ "," ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(~(~(_, first), _), second), _), last), _) => {
      AppRec(new Var("max", i -> (i -> (i -> i))), List(first, second, last))
    }

  }

  def max2: Parser[E] = "max(" ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(_, first), _), second), _) => {
      AppRec(new Var("max", i -> (i -> i)), List(first, second))
    }

  }

  def userDef: Parser[E] = name ~ "(" ~ term ~ ")" ^^ {
    case ~(~(~(name, _), arg), _) => {
      new App(new Var(name, i -> i), arg)
    }
  }

  def num: Parser[E] = """\d+""".r ^^ {
    case a => {
      new Var(a, i)
    }
  }

  def number: Parser[Int] = """\d+""".r ^^ { _.toInt }

  def term: Parser[E] = (negTerm | func | num | variable)

  def negTerm: Parser[E] = "(~ " ~ term ~ ")" ^^ {
    case ~(~(_, t), _) => {
      t //TODO: should actually apply the '~' before returning it
    }
  }

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

class Ref(f: Int, s: Int) {
  def first = f
  def second = s
  override def toString = "(" + f + ", " + s + ")"
}
