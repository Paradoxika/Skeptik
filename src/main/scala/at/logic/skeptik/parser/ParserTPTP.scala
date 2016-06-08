package at.logic.skeptik.parser


import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula.{All, And, Atom, Equivalence, Ex, FormulaEquality, Imp, Neg, Or}
import at.logic.skeptik.expression.term._
import at.logic.skeptik.parser.TPTPParsers.TPTPAST._
import at.logic.skeptik.parser.TPTPParsers.{TPTPLexical, TPTPTokens}

import scala.collection.immutable.Nil
import scala.collection.mutable.{Set, HashSet => MSet}
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
  * @author  Ezequiel Postan
  * @since   23.05.2016
  * @version 1.0
  * @note    This version does not support let expressions
  */

class UnexpectedEmptyTPTPFileException extends Exception("Unexpected Empty File")
class TPTPExtractException extends Exception("Unexpected Extract Exception")


/**
  * The BaseParserTPTP trait implements the common parsers shared
  * both by problems and proof objects described by the TPTP syntax.
  * They return an AST representation of the syntax, logic formulas
  * are translated to their Skeptik internal representation.
  */

// TODO: CHECK EQUALITY TYPE
trait BaseParserTPTP
extends TokenParsers with PackratParsers {

  /*
   * Unfortunately this varSet is needed for the creation of resolution
   * nodes in a future stage. This MUST be solved to delete the next three
   * members.
   */
  private var varSet : Set[Var] = new MSet[Var]()
  private def recordVar(v : String) {varSet += new Var(v,i)}
  def getSeenVars : Set[Var] = varSet.clone()
  def resetVarsSeen() : Unit = { varSet.clear() }

  val  lexical = new TPTPLexical
  type Tokens  = TPTPTokens

  // Parsing methods
  def parse[Target](input: String, parser: Parser[Target]) = {
    val fileContent = scala.io.Source.fromFile(input).mkString
    val tokens = new lexical.Scanner(fileContent)
    var t = new lexical.Scanner(fileContent)
    phrase(parser)(tokens)
  }

  def parseString[Target](input: Reader[Char], parser: Parser[Target]) = {
    val tokens = new lexical.Scanner(input)
    phrase(parser)(tokens)
  }

  def tokens(input: String) = {
    new lexical.Scanner(input)
  }

  def tokens(input: Reader[Char]) = {
    new lexical.Scanner(input)
  }

  def extract[Target](fileName : String, parser : Parser[Target]) : Target  =
    parse(fileName, parser) match {
      case Success(p2, _) => p2
      case Error(message, _) => throw new Exception("Error: " + message)
      case Failure(message, _) => throw new Exception("Failure: " + message)
    }


  /**
    * A simple implementation for the expansion of include directives
    *
    * TODO: Detect include loops
    * TODO: Analyze whether to track only the selected formulas
    *       or all the file (as done know). This is not trivial because
    *       thf and tff define types annotated formulas with the same
    *       name of the annotated formula.
    *
    * @param directives A list of TPTP directives (includes and/or annotated formulas)
    * @return           The expansion of all the includes (recursivelly) to the files
    */
  def expandIncludes(directives : List[TPTPDirective], parser: Parser[List[TPTPDirective]]) : List[TPTPDirective] = directives match {
    case List()                             => List.empty
    case IncludeDirective(fileName,_) :: ds => expandIncludes(extract(fileName,parser),parser) ++ ds
    case d                            :: ds => d :: expandIncludes(ds,parser)
  }

  // Actual Parsers
  import lexical._

  def TPTP_file: Parser[List[TPTPDirective]] = rep(TPTP_input)

  def TPTP_input: Parser[TPTPDirective] = annotated_formula | include

  def annotated_formula: Parser[AnnotatedFormula] = (
    tpi_annotated
      | thf_annotated
      | tff_annotated
      | fof_annotated
      | cnf_annotated
    )


  def include: Parser[IncludeDirective] = (
    (elem(Include) ~ elem(LeftParenthesis)) ~> elem("Single quoted", _.isInstanceOf[SingleQuoted])
      ~ opt((elem(Comma) ~ elem(LeftBracket)) ~> repsep(name,elem(Comma)) <~ elem(RightBracket))
      <~ (elem(RightParenthesis) ~ elem(Dot)) ^^ {
      case SingleQuoted(fileName) ~ Some(formulas) => IncludeDirective(fileName, formulas)
      case SingleQuoted(fileName) ~       _        => IncludeDirective(fileName, List.empty)
    }
  )

  def annotatedPattern(languageToken : Token, expectedFormula : Parser[RepresentedFormula]) =
    (elem(languageToken) ~ elem(LeftParenthesis)) ~> name ~ (elem(Comma) ~> formula_role <~ elem(Comma)) ~ expectedFormula ~ annotations <~ elem(RightParenthesis) ~ elem(Dot)

  private def toAnnotatedFormula(language: Language, name: Name,
                                 role: FormulaRole, formula: RepresentedFormula,
                                 annotations: Annotations) : AnnotatedFormula =
    new AnnotatedFormula(language,name,role,formula,annotations)

  def fof_annotated : Parser[AnnotatedFormula] = annotatedPattern(FOF,fof_formula) ^^
    { case name ~ role ~ formula ~ annotations => toAnnotatedFormula(FOF.chars,name,role,formula,annotations) }
  def cnf_annotated : Parser[AnnotatedFormula] = annotatedPattern(CNF,cnf_formula) ^^
    { case name ~ role ~ formula ~ annotations => toAnnotatedFormula(CNF.chars,name,role,formula,annotations) }
  def tff_annotated : Parser[AnnotatedFormula] = annotatedPattern(TFF,tff_formula) ^^
    { case name ~ role ~ formula ~ annotations => toAnnotatedFormula(TFF.chars,name,role,formula,annotations) }
  def thf_annotated : Parser[AnnotatedFormula] = annotatedPattern(THF,thf_formula) ^^
    { case name ~ role ~ formula ~ annotations => toAnnotatedFormula(THF.chars,name,role,formula,annotations) }
  def tpi_annotated : Parser[AnnotatedFormula] = annotatedPattern(TPI,tpi_formula) ^^
    { case name ~ role ~ formula ~ annotations => toAnnotatedFormula(TPI.chars,name,role,formula,annotations) }


  def name : Parser[String] = (
    atomic_word
      | elem("integer", _.isInstanceOf[Integer]) ^^ {_.chars}
    )
  def atomic_word: Parser[String] = (
    elem("lower word", _.isInstanceOf[LowerWord])           ^^ {_.chars}
      | elem("single quoted", _.isInstanceOf[SingleQuoted]) ^^ {_.chars}
    )

  def formula_role : Parser[String] = elem("Lower word", _.isInstanceOf[LowerWord]) ^^ {_.chars}

  def annotations : Parser[Annotations] =
    opt(elem(Comma) ~> source ~ optional_info) ^^ {
      case None => None
      case Some(src ~ info) => Some((src,info))
    }

  def source : Parser[Source] = general_term
  def optional_info : Parser[List[GeneralTerm]] =  opt(elem(Comma) ~> useful_info) ^^ {
    case None => List.empty
    case Some(x) => x
  }

  def useful_info: Parser[List[GeneralTerm]] = general_list

  // Non-logical data (GeneralTerm, General data)
  def general_term: Parser[GeneralTerm] = (
    general_list                              ^^ {x => GeneralTerm(List(Right(x)))}
      ||| general_data                              ^^ {x => GeneralTerm(List(Left(x)))}
      ||| general_data ~ elem(Colon) ~ general_term ^^ {case data ~ _ ~ gterm => GeneralTerm(Left(data) :: gterm.term)}
    )

  def general_list: Parser[List[GeneralTerm]] =
    elem(LeftBracket) ~> opt(general_terms) <~ elem(RightBracket) ^^ {
      case Some(gt)   => gt
      case _       => List.empty
    }
  def general_terms: Parser[List[GeneralTerm]] = rep1sep(general_term, elem(Comma))

  def general_data: Parser[GeneralData] = (
    atomic_word                                                   ^^ {GWord(_)}
      ||| general_function
      ||| variable                                                ^^ {GVar(_)}
      ||| number                                                  ^^ {GNumber(_)}
      ||| elem("Distinct object", _.isInstanceOf[DistinctObject]) ^^ {x => GDistinct(x.chars)}
      ||| formula_data                                            ^^ {GFormulaData(_)}
    )

  def variable: Parser[String] = elem("Upper word", _.isInstanceOf[UpperWord]) ^^ {_.chars}

  def number: Parser[String] = (
        elem("Integer" , _.isInstanceOf[Integer] ) ^^ {_.chars}
      | elem("Real"    , _.isInstanceOf[Real]    ) ^^ {_.chars}
      | elem("Rational", _.isInstanceOf[Rational]) ^^ {_.chars}
    )

  def general_function: Parser[GFunc] =
    atomic_word ~ elem(LeftParenthesis) ~ general_terms ~ elem(RightParenthesis) ^^ {
      case name ~ _ ~ args ~ _  => GFunc(name,args)
    }

  def formula_data : Parser[FormulaData] = (
    (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$thf"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      thf_formula <~ elem(RightParenthesis) ^^ {GFormulaDataFormula("$thf",_)}
      | (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$tff"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      tff_formula <~ elem(RightParenthesis) ^^ {GFormulaDataFormula("$tff",_)}
      | (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$fof"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      fof_formula <~ elem(RightParenthesis) ^^ {GFormulaDataFormula("$fof",_)}
      | (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$cnf"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      cnf_formula <~ elem(RightParenthesis) ^^ {GFormulaDataFormula("$cnf",_)}
      | (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$fot"))(_ => "Parse error in formulaData") ~ elem(LeftParenthesis)) ~>
      term <~ elem(RightParenthesis) ^^ {GFormulaDataTerm("$fot",_)}
    )

  def term: Parser[E] = (
    function_term
      ||| variable         ^^ {x => {recordVar(x);Variable(x)}}
      ||| conditional_term
      ||| let_term
    )

  def function_term: Parser[E] = (
    plain_term                                                  ^^ {case (name,args) => FunctionTerm(name,args)}
      | defined_plain_term                                      ^^ {case (name,args) => FunctionTerm(name,args)}
      | system_term                                             ^^ {case (name,args) => FunctionTerm(name,args)}
      | number                                                  ^^ {NumberTerm(_)}
      | elem("Distinct object", _.isInstanceOf[DistinctObject]) ^^ {x => DistinctObjectTerm(x.chars)} // TODO: How to encode this...
    )



  def plain_term: Parser[(String,List[E])] =
    constant ~ opt(elem(LeftParenthesis) ~> arguments <~ elem(RightParenthesis)) ^^ {
      case c ~ Some(x) => (c, x )//FunctionTerm(c,x)
      case c ~ _       => (c,Nil)//Constant(c)
    }

  def constant: Parser[String] = atomic_word

  def defined_plain_term: Parser[(String,List[E])] =
    atomic_defined_word ~ opt(elem(LeftParenthesis) ~> arguments <~ elem(RightParenthesis)) ^^ {
      case c ~ Some(x) => (c, x )//FunctionTerm(c,x)
      case c ~ _       => (c,Nil)//Constant(c)
    }

  def system_term: Parser[(String,List[E])] =
    atomic_system_word ~ opt(elem(LeftParenthesis) ~> arguments <~ elem(RightParenthesis)) ^^ {
      case c ~ Some(x) => (c, x )// FunctionTerm(c,x)
      case c ~ _       => (c,Nil)// Constant(c)
    }

  def arguments: Parser[List[E]] = rep1sep(term, elem(Comma))

  def conditional_term: Parser[E] =
    (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$ite_t"))(_ => "Error in Conditional Term") ~ elem(LeftParenthesis)) ~>
      tff_logic_formula ~ elem(Comma) ~ term ~ elem(Comma) ~ term <~ elem(RightParenthesis) ^^ {
      case formula ~ _ ~ thn ~ _ ~ els => ConditionalTerm(formula,thn,els)
    }

  // TODO: let terms currently do not accept sequents in the expanssion of formulas.
  def let_term : Parser[E] = failure("Let expressions are not supported")


  def atomic_defined_word: Parser[String] = elem("Dollar word", _.isInstanceOf[DollarWord]) ^^ {_.chars}
  def atomic_system_word: Parser[String] = elem("Dollar Dollar word", _.isInstanceOf[DollarDollarWord]) ^^ {_.chars}

  def file_name: Parser[String] = elem("single quoted", _.isInstanceOf[SingleQuoted]) ^^ {_.chars}



  // First-order atoms
  def atomic_formula: Parser[E] =
    plain_atomic_formula ||| defined_plain_formula ||| defined_infix_formula ||| system_atomic_formula

  def plain_atomic_formula :  Parser[E] = plain_term         ^^ {case (name,args) => Atom(name,args)}
  def defined_plain_formula : Parser[E] = defined_plain_term ^^ {case (name,args) => Atom(name,args)}
  def defined_infix_formula : Parser[E] =
    term ~ elem(Equals) ~ term ^^ {
      case t1 ~ _ ~ t2 => FormulaEquality(t1,t2)
    }
  def system_atomic_formula: Parser[E] = system_term ^^ {case (name,args) => Atom(name,args)}



  // We finally have the different  formula parsers
  ////////////////////////////////////////////////////
  // TPI Formulas
  ////////////////////////////////////////////////////
  def tpi_formula : Parser[RepresentedFormula] = fof_formula

  ////////////////////////////////////////////////////
  // FOF Formulas
  ////////////////////////////////////////////////////
  def fof_formula : Parser[RepresentedFormula] = (
    fof_logic_formula ^^ {SimpleFormula(_)}
      | fof_sequent
    )

  def fof_logic_formula : Parser[E] = fof_binary_formula ||| fof_unitary_formula

  def fof_binary_formula: Parser[E] = fof_binary_non_assoc ||| fof_binary_assoc

  // TODO: Check if this interpretation of the meaning of the symbols is right
  // p <~> q          is ¬ (p <=> q) where <=> is the equivalence
  // p ~|q and p ~& q are ¬ (p \/ q) and ¬ (p /\ q) respectively
  def fof_binary_non_assoc: Parser[E] = fof_unitary_formula ~ binary_connective ~ fof_unitary_formula ^^ {
    case left ~ Leftrightarrow      ~ right => Equivalence(left,right)
    case left ~ Rightarrow          ~ right => Imp(left,right)
    case left ~ Leftarrow           ~ right => Imp(right,left) // NOTE THE REVERSED PARAMETERS
    case left ~ Leftrighttildearrow ~ right => Neg(Equivalence(left,right))
    case left ~ TildePipe           ~ right => Neg(Or(left,right))
    case left ~ TildeAmpersand      ~ right => Neg(And(left,right))
  }

  def fof_binary_assoc: Parser[E] = fof_or_formula | fof_and_formula

  // Note that the type is PackratParser here and not Parser to handle left recursion
  lazy val fof_or_formula: PackratParser[E] = (
    fof_unitary_formula ~ elem(VLine) ~ fof_unitary_formula  ^^ {case left ~ _ ~ right => Or(left,right)}
      ||| fof_or_formula ~ elem(VLine) ~ fof_unitary_formula ^^ {case left ~ _ ~ right => Or(left,right)}
    )

  // Note that the type is PackratParser here and not Parser to handle left recursion
  lazy val fof_and_formula: PackratParser[E] = (
    fof_unitary_formula ~ elem(Ampersand) ~ fof_unitary_formula   ^^ {case left ~ _ ~ right => And(left,right)}
      ||| fof_and_formula ~ elem(Ampersand) ~ fof_unitary_formula ^^ {case left ~ _ ~ right => And(left,right)}
    )

  def fof_unitary_formula: Parser[E] = (
    elem(LeftParenthesis) ~> fof_logic_formula <~ elem(RightParenthesis)
      | fof_quantified_formula
      | fof_unary_formula
      | atomic_formula
    )

  def fof_quantified_formula: Parser[E] =
    fol_quantifier ~ elem(LeftBracket) ~ rep1sep(variable^^{x => {recordVar(x);Variable(x).asInstanceOf[Var]}},elem(Comma)) ~ elem(RightBracket) ~ elem(Colon) ~ fof_unitary_formula ^^ {
      case Exclamationmark ~ _ ~ vars ~ _ ~ _ ~ matrix => All(vars,matrix)
      case Questionmark    ~ _ ~ vars ~ _ ~ _ ~ matrix => Ex(vars,matrix)
    }

  def fol_quantifier: Parser[Token] = elem(Exclamationmark) | elem(Questionmark)
  def binary_connective: Parser[Token] = (
    elem(Leftrightarrow)
      | elem(Rightarrow)
      | elem(Leftarrow)
      | elem(Leftrighttildearrow)
      | elem(TildePipe)
      | elem(TildeAmpersand)
    )

  def fof_unary_formula: Parser[E] = (
    unary_connective ~ fof_unitary_formula ^^ {case Tilde ~ formula => Neg(formula)}
      | fol_infix_unary                    ^^ {case left  ~ right   => Neg(FormulaEquality(i)(left,right))}
    )

  def unary_connective: Parser[Token] = elem(Tilde)


  def fol_infix_unary: Parser[E ~ E] =
    term ~ elem(NotEquals) ~ term ^^ {
      case l ~ _ ~ r => this.~(l,r)
    }


  def fof_sequent: Parser[RepresentedFormula] = (
    fof_tuple ~ gentzen_arrow ~ fof_tuple ^^ {case t1 ~ _ ~ t2 => SimpleSequent(t1,t2)}
      ||| elem(LeftParenthesis) ~> fof_sequent <~ elem(RightParenthesis)
    )

  def gentzen_arrow: Parser[String] = elem(Minus) ~ elem(Minus) ~ elem(Rightarrow) ^^ {_ => ""}

  def fof_tuple: Parser[List[E]] =
    elem(LeftBracket) ~> repsep(fof_logic_formula, elem(Comma)) <~ elem(RightBracket)

  ////////////////////////////////////////////////////
  // CNF Formulas
  ////////////////////////////////////////////////////
  def cnf_formula : Parser[RepresentedFormula] = (
    elem(LeftParenthesis) ~> disjunction <~ elem(RightParenthesis)
      ||| disjunction
    ) ^^ {case (ant,suc) => SimpleSequent(ant,suc)}

  // Note that the type is PackratParser here and not Parser to handle left recursion
  lazy val disjunction: PackratParser[(List[E],List[E])] = (
    literal                                   ^^ {appendToListPair(_,(Nil,Nil))}
      ||| disjunction ~ elem(VLine) ~ literal ^^ {case dis ~ _ ~ l => appendToListPair(l,dis)}
    )

  private def appendToListPair(literal : Either[E,E], acumulators : (List[E],List[E])) : (List[E],List[E]) = literal match {
    case Left(Var("$true",_))   => (acumulators._1 , acumulators._2)
    case Left(l)                => (acumulators._1 ++ List(l) , acumulators._2)
    case Right(Var("$false",_)) => (acumulators._1 , acumulators._2)
    case Right(l)               => (acumulators._1 , acumulators._2 ++ List(l))
  }


  def literal: Parser[Either[E,E]] = (
    atomic_formula                      ^^ {Right(_)}
      ||| elem(Tilde) ~> atomic_formula ^^ {Left(_)}
      ||| fol_infix_unary               ^^ {case left ~ right => Left(FormulaEquality(i)(left,right))}
    )

  ////////////////////////////////////////////////////
  // TFF Formulas
  ////////////////////////////////////////////////////
  def tff_formula : Parser[RepresentedFormula] = failure("tff_formula parser not implemented")

  def tff_logic_formula : Parser[E] = failure("tff_logic_formula parser not implemented")


  ////////////////////////////////////////////////////
  // THF Formulas
  ////////////////////////////////////////////////////
  def thf_formula : Parser[RepresentedFormula] = failure("thf_formula parser not implemented")

  def thf_logic_formula : Parser[E] = failure("thf_logic_formula parser not implemented")
}












