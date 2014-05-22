package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{ HashMap => MMap }
import collection.mutable.{ HashSet => MSet }
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{ SequentProofNode => Node }
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.proof.sequent.resolution._

object ProofParserSPASS extends ProofParser[Node] with SPASSParsers

trait SPASSParsers
  extends JavaTokenParsers with RegexParsers {

  private var count = 0;

  private var proofMap = new MMap[Int, Node]

  //unused?
  private var exprMap = new MMap[Ref, E] //will map axioms/proven expressions to the location (line number) where they were proven

  private var varMap = new MMap[String, E] //will map variable names to an expression object for that variable

  //TODO: remove debugging lines

  //returns the actual proof
  def proof: Parser[Proof[Node]] = rep(line) ^^ {
    case list => {
      println("parsed! " + count)
      println(varMap)
      println(exprMap)
      val p = Proof(list.last)
      exprMap = new MMap[Ref, E]
      p
    }
  }

  def line: Parser[Node] = lineNum ~ "[" ~ number ~ ":" ~ inferenceRule ~ rep(lineRef) ~ "] ||" ~ sequent ^^ {
    //TODO: needs to change to use unifying resolution & other inference rules
    case ~(~(~(~(~(~(~(ln, _), _), _), "Inp"), _), _), seq) => {
      //val ax = new Axiom(Sequent(bigAnd(seq._1))(bigOr(seq._2)))

      val sA = addAntecedents(seq._1)

      val sS = addSuccedents(seq._2)

      val sFinal = sA union sS

      val ax = new Axiom(sA)
      proofMap += (ln -> ax)
      ax
    }

    // * //TODO: currently broken? Can't find implicit variable in either case.
    case ~(~(~(~(~(~(~(ln, _), _), _), "Res:"), refs), _), seq) => {
      def firstRef = refs.head
      def secondRef = refs.tail.head
      def firstNode = firstRef.first
      def secondNode = secondRef.first
      //        val unif: MSet[Var] = new MSet[Var]()
      //        val u: Set[E] = new MSet[E]()
      //        unif.add(exprMap.getOrElse(firstRef,  throw new Exception("Error!")))
      //        unif.add(exprMap.getOrElse(secondRef,  throw new Exception("Error!")))
      //val ax = UnifyingResolution(proofMap.getOrElse(firstNode, throw new Exception("Error!")), proofMap.getOrElse(secondNode, throw new Exception("Error!")), )
      val ax = UnifyingResolution(proofMap.getOrElse(firstNode, throw new Exception("Error!")), proofMap.getOrElse(secondNode, throw new Exception("Error!")))(Set())

      //results in:  Resolution: the conclusions of the given premises are not resolvable.

      proofMap += (ln -> ax)
      ax
    }

    //For now, treat the other inference rules as new axioms
    case ~(~(~(~(~(~(~(ln, _), _), _), _), refs), _), seq) => {
      //  val ax = new Axiom(Sequent(bigAnd(seq._1))(bigOr(seq._2)))

      val sA = addAntecedents(seq._1)

      val sS = addSuccedents(seq._2)

      val sFinal = sA union sS

      val ax = new Axiom(sA)
      proofMap += (ln -> ax)
      ax
    }
  }

  def sequent: Parser[(List[E], List[E])] = antecedent ~ "->" ~ succedent ~ "." ^^ {
    case ~(~(~(a, _), s), _) => {
      /*
      //This function maintains a map of the form ((proof line, clause position) -> clause).       
      def addToExprMap(lineNumber: Int, startPos: Int, exps: List[E]): Int = {
        if (exps.length > 1) {
          exprMap.getOrElseUpdate(new Ref(lineNumber, startPos), exps.head)
          addToExprMap(lineNumber, startPos + 1, exps.tail)
        } else if (exps.length == 1) {
          exprMap.getOrElseUpdate(new Ref(lineNumber, startPos), exps.head)
          startPos + 1
        } else {
          throw new Exception("Clause position failed to be mapped");
          -1
        }
      }

      addToExprMap(count, addToExprMap(count, 0, a), s)
	  */

      count = count + 1
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

  def lineNum: Parser[Int] = number

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

  def func: Parser[E] = equals | max | userDef | lessEquals | greaterEquals

  def equals: Parser[E] = "eq(" ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(_, first), _), second), _) => {
      //println("eq: " + first + " " + second)
      AppRec(new Var("eq", booleanFunctionType(2)), List(first, second)) //TODO: check
    }
  }

  def lessEquals: Parser[E] = "le(" ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(_, first), _), second), _) => {
      // println("le: " + first + " " + second)
      AppRec(new Var("le", booleanFunctionType(2)), List(first, second)) //TODO: check
    }
  }

  def greaterEquals: Parser[E] = "ge(" ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(_, first), _), second), _) => {
      //println("ge: " + first + " " + second)
      AppRec(new Var("ge", booleanFunctionType(2)), List(first, second)) //TODO: check
    }
  }

  def max: Parser[E] = "max(" ~ term ~ "," ~ term ~ "," ~ term ~ ")" ^^ {
    case ~(~(~(~(~(~(_, first), _), second), _), last), _) => {
      AppRec(new Var("max", booleanFunctionType(3)), List(first, second, last)) //TODO: check
    }

  }

  def userDef: Parser[E] = name ~ "(" ~ term ~ ")" ^^ {
    case ~(~(~(name, _), arg), _) => {
      //println("userdef: " + name + " - " + arg)      
      new App(new Var(name, new Arrow(o, o)), arg)
    }
  }

  def num: Parser[E] = """\d+""".r ^^ {
    case a => {
      // println("num: " + a)
      new Var(a, o) //TODO: check
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
      varMap.getOrElseUpdate(s, new Var(s.toString, o))
    }
  }

  def name: Parser[String] = "[a-zA-Z0-9]+".r ^^ {
    case s => {
      //  println("name: " + s)
      s
    }
  }

  def addAntecedents(antes: List[E]): Sequent = {
    if (antes.length > 1) {
      val s1 = antes.head +: addAntecedents(antes.tail)
      s1
    } else if (antes.length == 1) {
      val s0 = Sequent()()
      val s1 = s0 + antes.head
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
}
