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
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents

object SequentParser extends SequentParser {
  def apply(input: String): Sequent = parseAll(line, input) match {
    case Success(result, _) => result
    case failure: NoSuccess => scala.sys.error(failure.msg)
  }
}

trait SequentParser
  extends JavaTokenParsers with RegexParsers with checkUnifiableVariableName {

  def line: Parser[Sequent] = number ~ ": {" ~ sequent ~ lineSuffix ^^ {
    case ~(~(~(n, _), s), _) => {
      newSequentFromLists(s._1, s._2)
    }
  }

  def newSequentFromLists(ant: List[E], suc: List[E]): Sequent = {
    val sA = addAntecedents(ant)
    val sS = addSuccedents(suc)
    val sFinal = sA union sS
    sFinal
  }

  def lineSuffix: Parser[String] = "}" ~ ":" ~ name ~ "(" ~ repsep(number, ",") ~ ")[]" ^^ {
    case _ => "" //none of this matters
  }

  def sequent: Parser[(List[E], List[E])] = antecedent ~ "⊢" ~ succedent ^^ {
    case ~(~(a, _), s) => {
      (a, s)
    }
  }

  def antecedent: Parser[List[E]] = repsep(term, ",")
  def succedent: Parser[List[E]] = repsep(term, ",")

  def func: Parser[E] = "(" ~ name ~ rep(term) ~ ")" ^^ {
    case ~(~(~(_, name), args), _) => {
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
      throw new ParserException("Sequent Parser: Arrow creation failed")
    }
  }

  def num: Parser[E] = """\d+""".r ^^ {
    case a => {
      new Var(a, i)
    }
  }

  def number: Parser[Int] = """\d+""".r ^^ { _.toInt }

  def term: Parser[E] = (func | num | variable) ^^ {
    case x => {
      x
    }
  }

  def variable: Parser[E] = name ^^ {
    case s => {
      Var(s, i)
    }
  }

  def name: Parser[String] = "[a-zA-Z0-9]+".r ^^ {
    case s => {
      s
    }
  }

}


