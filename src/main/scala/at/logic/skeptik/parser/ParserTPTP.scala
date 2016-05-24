package at.logic.skeptik.parser


import collection.mutable.{HashMap => MMap}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{Axiom, R, UncheckedInference}
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.parser.TPTPParsers.{TPTPLexical, TPTPTokens}

import scala.util.parsing.combinator.syntactical.TokenParsers
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.input.Reader


/**
  * This modules describe the TPTP syntax as descrobed in
  * www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html
  *
  * The non terminals don't follow camelcase convention to
  * reflect the grammar in a more natural way.
  *
  * @author Ezequiel Postan
  * @since 23.05.2016
  */

class UnexpectedEmptyTPTPFileException extends Exception("Unexpected Empty File")
class TPTPExtractException extends Exception("Unexpected Extract Exception")


object ProofParserTPTP   extends ProofParser[Node] with ProofParserTPTP
object ProblemParserTPTP extends ProblemParserTPTP

/**
  * The BaseParserTPTP implements the common parsers shared both
  * by problems and proof objects described by the TPTP syntax
  */
trait BaseParserTPTP
extends TokenParsers with PackratParsers {

  val  lexical = new TPTPLexical
  type Tokens  = TPTPTokens

  // Parsing methods
  def parse[Target](input: String, parser: Parser[Target]) = {
    val tokens = new lexical.Scanner(input)
    phrase(parser)(tokens)
  }

  def parse[Target](input: Reader[Char], parser: Parser[Target]) = {
    val tokens = new lexical.Scanner(input)
    phrase(parser)(tokens)
  }

  def tokens(input: String) = {
    new lexical.Scanner(input)
  }

  def tokens(input: Reader[Char]) = {
    new lexical.Scanner(input)
  }


  // Actual Parsers
  import lexical._

  def include: Parser[(String,List[String])] = (
    (elem(Include) ~ elem(LeftParenthesis)) ~> elem("Single quoted", _.isInstanceOf[SingleQuoted])
      ~ opt((elem(Comma) ~ elem(LeftBracket)) ~> repsep(name,elem(Comma)) <~ elem(RightBracket))
      <~ (elem(RightParenthesis) ~ elem(Dot)) ^^ {
      case SingleQuoted(data) ~ Some(names) => (data, names)
      case SingleQuoted(data) ~     _       => (data, List.empty)
    }
  )

  def annotatedPattern(languageToken : Token, expectedFormula : Parser[_]) =
    (elem(languageToken) ~ elem(LeftParenthesis)) ~> name ~ (elem(Comma) ~> formula_role <~ elem(Comma)) ~ expectedFormula ~ annotations <~ elem(RightParenthesis) ~ elem(Dot) ^^ {
      case name ~ role ~ formula ~ annotations => (name,role,formula,annotations)
    }

  def fof_annotated = annotatedPattern(FOF,fof_formula)
  def cnf_annotated = annotatedPattern(CNF,cnf_formula)
  def tff_annotated = annotatedPattern(TFF,tff_formula)
  def thf_annotated = annotatedPattern(THF,thf_formula)
  def tpi_annotated = annotatedPattern(TPI,tpi_formula)


  def name : Parser[String] = (
    atomic_word
    | elem("integer", _.isInstanceOf[Integer]) ^^ {_.chars}
  )
  def atomic_word: Parser[String] = (
    elem("lower word", _.isInstanceOf[LowerWord]) ^^ {_.chars}
    | elem("single quoted", _.isInstanceOf[SingleQuoted]) ^^ {_.chars}
  )

  def formula_role : PackratParser[String] = {
    def isRecognizedAsFormulaRole(token : Token): Boolean = {
      val acceptedRoles = List("axiom" , "hypothesis" , "definition" , "assumption" ,
                               "lemma" , "theorem" , "corollary" , "conjecture",
                               "negated_conjecture" , "plain" , "type" , "fi_domain" ,
                               "fi_functors" , "fi_predicates" , "unknown")
      token.isInstanceOf[LowerWord] &&  acceptedRoles.contains(token.chars)
    }
    val expectedWord = "axiom, hypothesis, definition, assumption, lemma, theorem, corollary, conjecture, " +
                       "negated_conjecture, plain, type, fi_domain, fi_functors, fi_predicates or unknown"
    elem(expectedWord, isRecognizedAsFormulaRole) ^^ {_.chars}
  }

  def annotations = failure("Annotation Paeser not defined")

  /*
  type Source       = String
  type OptionalInfo = List[UsefulInfo]
  type UsefulInfo   = (String,String)

  def annotations : Parser[Option[(Source,OptionalInfo)]] =
    opt(elem(Comma) ~> source ~ optional_info) ^^ {
      case None => None
      case Some(src ~ info) => Some((src,info))
    }

  def source : PackratParser[Source] = general_term
  def optional_info : Parser[OptionalInfo] =  opt(elem(Comma) ~> useful_info) ^^ {
    case None => List.empty
    case Some(x) => x
  }

  def useful_info: Parser[List[UsefulInfo]] = general_list

  // Non-logical data (GeneralTerm, General data)
  def general_term: Parser[] = (
          general_list                              ^^ {x => Commons.GeneralTerm(List(Right(x)))}
      ||| general_data                              ^^ {x => Commons.GeneralTerm(List(Left(x)))}
      ||| general_data ~ elem(Colon) ~ general_term ^^ {case data ~ _ ~ gterm => Commons.GeneralTerm(Left(data) :: gterm.term)}
    )

  def general_list: Parser[List[Commons.GeneralTerm]] =
    elem(LeftBracket) ~> opt(general_terms) <~ elem(RightBracket) ^^ {
      case Some(gt)   => gt
      case _       => List.empty
    }
  def general_terms: Parser[List[Commons.GeneralTerm]] = rep1sep(general_term, elem(Comma))

  def general_data: Parser[Commons.GeneralData] = (
          atomic_word                                             ^^ {Commons.GWord(_)}
      ||| general_function
      ||| variable                                                ^^ {Commons.GVar(_)}
      ||| number                                                  ^^ {Commons.GNumber(_)}
      ||| elem("Distinct object", _.isInstanceOf[DistinctObject]) ^^ {x => Commons.GDistinct(x.chars)}
      ||| formula_data                                             ^^ {Commons.GFormulaData(_)}
    )

  def variable: Parser[Commons.Variable] = elem("Upper word", _.isInstanceOf[UpperWord]) ^^ {_.chars}
  def number: Parser[Commons.Number] = (
        elem("Integer" , _.isInstanceOf[Integer] ) ^^ {case i => Commons.IntegerNumber(i.asInstanceOf[Integer].value)}
      | elem("Real"    , _.isInstanceOf[Real]    ) ^^ {x => Commons.DoubleNumber((x.asInstanceOf[Real].coeff.toString + "E" + x.asInstanceOf[Real].exp.toString).toDouble)}
      | elem("Rational", _.isInstanceOf[Rational]) ^^ {case r => Commons.RationalNumber(r.asInstanceOf[Rational].p,r.asInstanceOf[Rational].q)}
    )

  def general_function: Parser[Commons.GFunc] =
    atomic_word ~ elem(LeftParenthesis) ~ general_terms ~ elem(RightParenthesis) ^^ {
      case name ~ _ ~ args ~ _  => Commons.GFunc(name,args)
    }

  def formula_data: Parser[Commons.FormulaData] = (
    (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$thf"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      thf_formula <~ elem(RightParenthesis) ^^ {Commons.THFData(_)}
      | (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$tff"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      tff_formula <~ elem(RightParenthesis) ^^ {Commons.TFFData(_)}
      | (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$fof"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      fof_formula <~ elem(RightParenthesis) ^^ {Commons.FOFData(_)}
      | (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$cnf"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      cnf_formula <~ elem(RightParenthesis) ^^ {Commons.CNFData(_)}
      | (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$fot"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      term <~ elem(RightParenthesis) ^^ {Commons.FOTData(_)}
    )
*/




  // We finally have the different  formula parsers
  def tpi_formula = fof_formula
  def fof_formula = failure("fof_formula parser not implemented")
  def cnf_formula = failure("cnf_formula parser not implemented")
  def tff_formula = failure("tff_formula parser not implemented")
  def thf_formula = failure("thf_formula parser not implemented")


}

trait ProblemParserTPTP
extends BaseParserTPTP {
}

trait ProofParserTPTP
extends BaseParserTPTP {

  private var varMap   = new MMap[String,E]
  private var exprMap  = new MMap[String,E]
  private var proofMap = new MMap[String,Node]

  def reset() : Unit = {
    varMap.clear()
    exprMap.clear()
    proofMap.clear()
  }

  //returns the actual proof
  def proof: Parser[Proof[Node]] = TPTP_file ^^ { p => if (p.nonEmpty) p.last
                                                       else throw new UnexpectedEmptyTPTPFileException                                       }

  def read(filename: String) : Proof[Node] = {
    val p : Proof[Node] = parse(filename,proof) match {
      case Success(p2,_)      => p2
      case Error(message,_)   => throw new Exception("Error: " + message)
      case Failure(message,_) => throw new Exception("Failure: " + message)
    }
    reset()
    p
  }



  def TPTP_file  : Parser[List[Proof[Node]]] = ???
  def TPTP_input : Parser[Proof[Node]] = ???


  def annotated_formula : Parser[Proof[Node]] = ???

}


