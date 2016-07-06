package at.logic.skeptik.parser

import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula.{All, And, Atom, ConditionalFormula, Equivalence, Ex, False, FormulaEquality, Imp, Neg, Or, True}
import at.logic.skeptik.expression.term._
import at.logic.skeptik.parser.TPTPParsers.TPTPAST._
import at.logic.skeptik.parser.TPTPParsers.{TPTPLexical, TPTPTokens}

import scala.collection.immutable.Nil
import scala.collection.mutable.{Set, HashMap => MMap, HashSet => MSet}
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
  private def recordVar(v : String,t : T) {varSet += new Var(v,t)}
  def getSeenVars : Set[Var] = varSet.clone()
  def resetVarsSeen() : Unit = { varSet.clear(); typedExpressions.clear() }

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

  def TPTP_file: Parser[List[TPTPDirective]] = rep(TPTP_input) ^^ {List.concat(_ :_*)}

  def TPTP_input: Parser[List[TPTPDirective]] = (annotated_formula ^^ {List(_)} | include) ^^{List.concat(_)}

  def annotated_formula: Parser[AnnotatedFormula] = (
    tpi_annotated
      | thf_annotated
      | tff_annotated
      | fof_annotated
      | cnf_annotated
    )


  def include: Parser[List[TPTPDirective]] = (
    (elem(Include) ~ elem(LeftParenthesis)) ~> elem("Single quoted", _.isInstanceOf[SingleQuoted])
      ~ opt((elem(Comma) ~ elem(LeftBracket)) ~> repsep(name,elem(Comma)) <~ elem(RightBracket))
      <~ (elem(RightParenthesis) ~ elem(Dot)) ^^ {
      case SingleQuoted(fileName) ~ Some(formulas) => expandIncludes(List(IncludeDirective(fileName, formulas)),TPTP_file)
      case SingleQuoted(fileName) ~       _        => expandIncludes(List(IncludeDirective(fileName, List.empty)),TPTP_file)
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
      ||| variable         ^^ {stringToVariable(_)}
      ||| conditional_term
      ||| let_term
    )

  private def stringToVariable(x: String) : E =
    if(typedExpressions contains x) {
      recordVar(x,typedExpressions(x))
      TypedVariable(x,typedExpressions(x))
    } else {
      recordVar(x)
      Variable(x)
    }

  def function_term: Parser[E] = (
    plain_term                                                  ^^ {case (name,args) => toFunctionTerm(name,args)}
      | defined_plain_term                                      ^^ {case (name,args) => toFunctionTerm(name,args)}
      | system_term                                             ^^ {case (name,args) => toFunctionTerm(name,args)}
      | number                                                  ^^ {NumberTerm(_)}
      | elem("Distinct object", _.isInstanceOf[DistinctObject]) ^^ {x => DistinctObjectTerm(x.chars)} // TODO: How to encode this...
    )

  private def toFunctionTerm(name : String , arguments : List[E]) : E =
    if(arguments.isEmpty && name == "$true") True()
    else if(arguments.isEmpty && name == "$false") False()
    else if(typedExpressions contains name) FunctionTerm(name,typedExpressions(name),arguments)
    else FunctionTerm(name,arguments)

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
  def defined_plain_formula : Parser[E] = defined_plain_term ^^ {case (name,args) => if(args.isEmpty && name == "$true") True()
                                                                                     else if(args.isEmpty && name == "$false") False()
                                                                                     else Atom(name,args)
                                                                }


  def defined_infix_formula : Parser[E] =
    term ~ elem(Equals) ~ term ^^ {
      case t1 ~ _ ~ t2 => FormulaEquality(t1.t)(t1,t2)
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
      | fol_infix_unary                    ^^ {case left  ~ right   => Neg(FormulaEquality(left.t)(left,right))}
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
    case Left(x)  if x == True()  => acumulators
    case Left(l)                  => (acumulators._1 ++ List(l) , acumulators._2)
    case Right(x) if x == False() => acumulators
    case Right(l)                 => (acumulators._1 , acumulators._2 ++ List(l))
  }


  def literal: Parser[Either[E,E]] = (
    atomic_formula                      ^^ {Right(_)}
      ||| elem(Tilde) ~> atomic_formula ^^ {Left(_)}
      ||| fol_infix_unary               ^^ {case left ~ right => Left(FormulaEquality(left.t)(left,right))}
    )

  ////////////////////////////////////////////////////
  // TFF Formulas
  ////////////////////////////////////////////////////
  val typedExpressions = MMap[String,T]()

  def tff_formula : Parser[RepresentedFormula] = (
    tff_logic_formula  ^^ {SimpleFormula(_)}
      | tff_typed_atom
      | tff_sequent
    )

  def tff_logic_formula : Parser[E] = tff_binary_formula | tff_unitary_formula

  def tff_binary_formula: Parser[E]   = tff_binary_non_assoc | tff_binary_assoc
  def tff_binary_non_assoc: Parser[E] = tff_unitary_formula ~ binary_connective ~ tff_unitary_formula ^^ {
    case left ~ Leftrightarrow      ~ right => Equivalence(left,right)
    case left ~ Rightarrow          ~ right => Imp(left,right)
    case left ~ Leftarrow           ~ right => Imp(right,left)
    case left ~ Leftrighttildearrow ~ right => Neg(Equivalence(left,right))
    case left ~ TildePipe           ~ right => Neg(Or(left,right))
    case left ~ TildeAmpersand      ~ right => Neg(And(left,right))
  }

  def tff_binary_assoc: Parser[E] = tff_or_formula | tff_and_formula

  lazy val tff_or_formula: PackratParser[E] = (
    tff_unitary_formula ~ elem(VLine) ~ tff_unitary_formula       ^^ {case left ~ _ ~ right => Or(left,right)}
      ||| tff_or_formula      ~ elem(VLine) ~ tff_unitary_formula ^^ {case left ~ _ ~ right => Or(left,right)}
    )

  lazy val tff_and_formula: PackratParser[E] = (
    tff_unitary_formula ~ elem(Ampersand) ~ tff_unitary_formula       ^^ {case left ~ _ ~ right => And(left,right)}
      ||| tff_and_formula     ~ elem(Ampersand) ~ tff_unitary_formula ^^ {case left ~ _ ~ right => And(left,right)}
    )

  def tff_unitary_formula: Parser[E] = (
    tff_quantified_formula
      | tff_unary_formula
      | tff_conditional
      | tff_let
      | atomic_formula
      | elem(LeftParenthesis) ~> tff_logic_formula <~ elem(RightParenthesis)
    )


  def tff_quantified_formula: Parser[E] =
    fol_quantifier ~ elem(LeftBracket) ~ rep1sep(tff_variable, elem(Comma)) ~ elem(RightBracket) ~ elem(Colon) ~ tff_unitary_formula ^^ {
      case Exclamationmark ~ _ ~ vars ~ _ ~ _ ~ matrix => All(vars,matrix)
      case Questionmark    ~ _ ~ vars ~ _ ~ _ ~ matrix => Ex(vars,matrix)
    }

  def tff_variable: Parser[Var] = (
    tff_typed_variable
      | failure("Expected type not found for quantified variable")
    // Here the failure is replacing the option of an untyped variable.
    // We don't allow the absence of type because we can't infer the type.
    )

  def tff_typed_variable: Parser[Var] =
    variable ~ elem(Colon) ~ tff_atomic_type ^^ {case variable ~ _ ~ typ  => recordVar(variable,typ); typedExpressions += (variable -> typ);  TypedVariable(variable, typ).asInstanceOf[Var] }

  def tff_unary_formula: Parser[E] = (
    unary_connective ~ tff_unitary_formula ^^ {case Tilde ~ formula => Neg(formula)}
      | fol_infix_unary                    ^^ {case left  ~ right   => Neg(FormulaEquality(left.t)(left, right))}
    )

  def tff_conditional: Parser[E] =
    (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$ite_f"))(_ => "Error in tffConditional") ~ elem(LeftParenthesis)) ~>
      tff_logic_formula ~ elem(Comma) ~ tff_logic_formula ~ elem(Comma) ~ tff_logic_formula <~ elem(RightParenthesis) ^^ {
      case cond ~ _ ~ thn ~ _ ~ els => ConditionalFormula(cond,thn,els)
    }

  // There are many issues to represent let expressions, but they are almost never used in real problems' description.
  // Only 2 files in over 20000 present in the TPTP problem library use let expressions so we decided not to support them.
  def tff_let: Parser[E] = failure("TFF let is not defined")

  def tff_sequent: Parser[RepresentedFormula] = (
    tff_tuple ~ gentzen_arrow ~ tff_tuple ^^ {case t1 ~ _ ~ t2 => SimpleSequent(t1,t2)}
      ||| elem(LeftParenthesis) ~> tff_sequent <~ elem(RightParenthesis)
    )

  def tff_tuple: Parser[List[E]] = repsep(tff_logic_formula, elem(Comma))

  def tff_typed_atom: Parser[RepresentedFormula] = (
    tff_untyped_atom ~ elem(Colon) ~ tff_top_level_type ^^ {case atom ~ _ ~ typ => typedExpressions += (atom -> typ) ; SimpleType(atom, typ)}
      | elem(LeftParenthesis) ~> tff_typed_atom <~ elem(RightParenthesis)
    )

  def tff_untyped_atom: Parser[String] = atomic_word | atomic_system_word

  def tff_top_level_type: Parser[T] = (
    tff_atomic_type
      ||| tff_mapping_type
      ||| tff_quantified_type
      ||| elem(LeftParenthesis) ~> tff_top_level_type <~ elem(RightParenthesis)
    )

  // Skeptik's type system does not support quantified types. So we don't support this part of the grammar.
  def tff_quantified_type: Parser[T] = failure("Quantified types currently undefined")
    /*
    (elem(Exclamationmark) ~ elem(Arrow)) ~>
      elem(LeftBracket) ~ rep1sep(tff_typed_variable, elem(Comma)) ~ elem(RightBracket) ~ elem(Colon) ~ tff_monotype ^^ {
      case _ ~ vars ~ _ ~ _ ~ typ => QuantifiedType(vars, typ)
    }*/

  def tff_monotype: Parser[T] = (
    tff_atomic_type
      | elem(LeftParenthesis) ~> tff_mapping_type <~ elem(RightParenthesis)
    )

  def tff_unitary_type: Parser[T] = (
    tff_atomic_type
      | elem(LeftParenthesis) ~> tff_xprod_type <~ elem(RightParenthesis)
    )

  // Skeptik's tyoe system does not support the parametrized types of the TPTP syntax, so they are not supported.
  def tff_atomic_type: Parser[T] = (
    (atomic_word | defined_type | variable) ^^ {t => if(t == "$i") i else if(t == "$o") o else AtomicType(t)}
      | failure("Unsupported type structure")
    /*atomic_word ~ elem(LeftParenthesis) ~ tff_type_arguments <~ elem(RightParenthesis) ^^ {
      case name ~ _ ~ args => AtomicType(name, args)
    }*/
    )

  def tff_type_arguments: Parser[List[T]] = rep1sep(tff_atomic_type, elem(Comma))

  def tff_mapping_type: Parser[T] =
    tff_unitary_type ~ elem(Arrow) ~ tff_atomic_type    ^^ {case l ~ _ ~ r => addToEnd(l,r) }

  private def addToEnd(dom : T, cod : T) : T = {
    import at.logic.skeptik.expression.Arrow
    dom match {
      case Arrow(s, t) => s -> addToEnd(t, cod)
      case other       => other -> cod
    }
  }

  // NOTE: Skeptik does not support product types, but according to the syntax this types are used only
  //       in the domain of mapping types, so we translate them curryfied.
  lazy val tff_xprod_type: PackratParser[T] = (
    tff_unitary_type ~ elem(Star) ~ tff_atomic_type       ^^ {case l ~ _ ~ r => addToEnd(l,r)}
      ||| tff_xprod_type   ~ elem(Star) ~ tff_atomic_type ^^ {case l ~ _ ~ r => addToEnd(l,r)}
    )

  def defined_type: Parser[String] = atomic_defined_word
  def system_type: Parser[String]  = atomic_system_word



  ////////////////////////////////////////////////////
  // THF Formulas
  ////////////////////////////////////////////////////
  /*
  * In this fragment we modified the grammar and separated types from formulas.
  * In the TPTP syntax a logic formula in THF can be a type formula. We can't manage this
  * in our data structures so we took them out and decided to parse types as thf formulas
  * in the same way it is done in TFF.
  */

  def thf_formula : Parser[RepresentedFormula] = (
    thf_logic_formula    ^^ {SimpleFormula(_)}
      | thf_sequent
      | thf_type_formula
      | thf_subtype
    )

  def thf_logic_formula : Parser[E] = (
    thf_binary_formula
      ||| thf_unitary_formula
    )

  def thf_binary_formula:Parser[E] = thf_binary_pair | thf_binary_tuple //| thf_binary_type ^^ {thf.BinType(_)}

  def thf_pair_connective: Parser[Token] = (
    elem(Equals)
      | elem(NotEquals)
      | binary_connective
    )

  def thf_binary_pair:Parser[E] = thf_unitary_formula ~ thf_pair_connective ~ thf_unitary_formula ^^ {
    case left ~ Equals              ~ right => FormulaEquality(left.t)(left,right)
    case left ~ NotEquals           ~ right => Neg(FormulaEquality(left.t)(left, right))
    case left ~ Leftrightarrow      ~ right => Equivalence(left, right)
    case left ~ Rightarrow          ~ right => Imp(left, right)
    case left ~ Leftarrow           ~ right => Imp(right,left)
    case left ~ Leftrighttildearrow ~ right => Neg(Equivalence(left, right))
    case left ~ TildePipe           ~ right => Neg(Or(left, right))
    case left ~ TildeAmpersand      ~ right => Neg(And(left, right))
  }

  def thf_binary_tuple: Parser[E] = thf_or_formula | thf_and_formula | thf_apply_formula

  lazy val thf_or_formula: PackratParser[E] = (
    thf_unitary_formula ~ elem(VLine) ~ thf_unitary_formula ^^ {case left ~ _ ~ right => Or(left, right)}
      ||| thf_or_formula ~ elem(VLine) ~ thf_unitary_formula      ^^ {case left ~ _ ~ right => Or(left, right)}
    )

  lazy val thf_and_formula: PackratParser[E] = (
    thf_unitary_formula ~ elem(Ampersand) ~ thf_unitary_formula ^^ {case left ~ _ ~ right => And(left, right)}
      ||| thf_and_formula ~ elem(Ampersand) ~ thf_unitary_formula     ^^ {case left ~ _ ~ right => And(left, right)}
    )

  lazy val thf_apply_formula: PackratParser[E] = (
    thf_unitary_formula ~ elem(Application) ~ thf_unitary_formula ^^ {case left ~ _ ~ right => App(left, right)}
      ||| thf_apply_formula ~ elem(Application) ~ thf_unitary_formula   ^^ {case left ~ _ ~ right => App(left, right)}
    )

  def thf_unitary_formula: Parser[E] = (
    thf_quantified_formula
      | thf_unary_formula
      | thf_let
      | thf_conditional
      | thf_atom
      | elem(LeftParenthesis) ~> thf_logic_formula <~ elem(RightParenthesis)
    )

  def thf_let = failure("THF let expressions are not supported")

  def thf_quantified_formula: Parser[E] =
    thf_quantifier ~ elem(LeftBracket) ~ rep1sep(thf_variable, elem(Comma)) ~ elem(RightBracket) ~ elem(Colon) ~ thf_unitary_formula ^^ {
      //case (Exclamationmark ~ Arrow) ~ _ ~ varList ~ _ ~ _ ~ matrix => thf.Quantified(thf.!>,varList,matrix)
      //case (Questionmark ~ Star)     ~ _ ~ varList ~ _ ~ _ ~ matrix => thf.Quantified(thf.?*,varList,matrix)
      //case (Application ~ Plus)      ~ _ ~ varList ~ _ ~ _ ~ matrix => thf.Quantified(thf.@+,varList,matrix)
      //ase (Application ~ Minus)     ~ _ ~ varList ~ _ ~ _ ~ matrix => thf.Quantified(thf.@-,varList,matrix)
      case Exclamationmark           ~ _ ~ varList ~ _ ~ _ ~ matrix => All(varList,matrix)
      case Questionmark              ~ _ ~ varList ~ _ ~ _ ~ matrix => Ex(varList,matrix)
      case Lambda                    ~ _ ~ varList ~ _ ~ _ ~ matrix => AbsRec(varList,matrix)
    }

  def thf_quantifier: Parser[Token] = (
    //elem(Exclamationmark) ~ elem(Arrow)
    //  | elem(Questionmark) ~ elem(Star)
    //  | elem(Application) ~ elem(Plus)
    //  | elem(Application) ~ elem(Minus)
    elem(Lambda)
      | fol_quantifier
    )


  def thf_variable: Parser[Var] =(
    thf_typed_variable
      | failure("Expected type not found for quantified variable")
    )

  def thf_typed_variable: Parser[Var] =
    variable ~ elem(Colon) ~ thf_top_level_type ^^ {
      case vari ~ _ ~ typ => recordVar(vari,typ); typedExpressions += (vari -> typ);TypedVariable(vari, typ).asInstanceOf[Var]
    }

  def thf_unary_formula: Parser[E] = thf_unary_connective ~ elem(LeftParenthesis) ~ thf_logic_formula <~ elem(RightParenthesis) ^^ {
    case Tilde                               ~ _ ~ formula => Neg(formula)
    //case (Exclamationmark ~ Exclamationmark) ~ _ ~ formula => thf.Unary(thf.!!, formula)
    //case (Questionmark ~ Questionmark)       ~ _ ~ formula => thf.Unary(thf.??, formula)
  }

  def thf_atom: Parser[E] = (
    term
      | thf_conn_term
    )

  def thf_conn_term: Parser[E] = failure("Undefined thf atom. Term expected but connective found" )
  def assoc_connective: Parser[Token] = elem(VLine) | elem(Ampersand)

  def thf_unary_connective: Parser[Any] = (
    unary_connective
      | elem(Exclamationmark) ~ elem(Exclamationmark)
      | elem(Questionmark) ~ elem(Questionmark)
    )


  def thf_conditional: Parser[E] = (
    (acceptIf(x => x.isInstanceOf[DollarWord] && x.chars.equals("$ite_f"))(_ => "Parse error in thfConditional") ~ elem(LeftParenthesis))
      ~> thf_logic_formula ~ elem(Comma) ~ thf_logic_formula ~ elem(Comma) ~ thf_logic_formula  <~ elem(RightParenthesis) ^^ {
      case cond ~ _ ~ thn ~ _ ~ els => ConditionalFormula(cond,thn,els)
    }
    )


  def thf_type_formula: Parser[SimpleType] = (
    thf_typeable_formula ~ elem(Colon) ~ thf_top_level_type ^^ {
      case formula ~ _ ~ typ => typedExpressions += (formula -> typ); SimpleType(formula,typ)
    }
    | elem(LeftParenthesis) ~> thf_type_formula <~ elem(RightParenthesis)
    )

  // We had to modify this from the grammar, in theory this parser should
  // be implemented as the commented part, but that wouldn't be translatable
  // to our data structures
  def thf_typeable_formula: Parser[String] = (
    atomic_word
      | atomic_system_word
    )/*(
    thf_atom
      | elem(LeftParenthesis) ~> thf_logic_formula <~ elem(RightParenthesis)
    )*/

  def subtype_sign: Parser[String] = repN(2,elem(LessSign)) ^^ { _  => ""}
  // Subtypes can't be represented in Skeptik's type sysntem, we left this unsupported for now.
  def thf_subtype: Parser[SimpleType] = failure("Subtypes are not supported")/*constant ~ subtype_sign ~ constant ^^ {
    case l ~ _ ~ r => ???
  }*/

  def thf_top_level_type: Parser[T] = (
    tff_atomic_type
      ||| thf_mapping_type
      ||| elem(LeftParenthesis) ~> thf_top_level_type <~ elem(RightParenthesis)
    )
  def thf_unitary_type: Parser[T] = thf_top_level_type //thfUnitaryFormula
  def thf_binary_type: Parser[T] = thf_mapping_type | thf_xprod_type | thf_union_type

  lazy val thf_mapping_type: PackratParser[T] = (
    thf_unitary_type ~ elem(Arrow) ~ thf_unitary_type       ^^ {case l ~ _ ~ r => l -> r}
      ||| thf_unitary_type ~ elem(Arrow) ~ thf_mapping_type ^^ {case l ~ _ ~ typ => l -> typ}
    )

  lazy val thf_xprod_type: PackratParser[T] = (
    thf_unitary_type ~ elem(Star) ~ thf_unitary_type       ^^ {case  l  ~ _ ~ r => addToEnd(l,r)}
      ||| thf_xprod_type   ~ elem(Star) ~ thf_unitary_type ^^ {case typ ~ _ ~ r => addToEnd(typ,r)}
    )

  // Type union can't be represented in Skeptik's type system so we left this undefined.
  lazy val thf_union_type: PackratParser[T] = failure("Union types are not supported")/*(
    thf_unitary_type ~ elem(Plus) ~ thf_unitary_type ^^ {case l ~ _ ~ r => +(l,r)}
      ||| thf_union_type   ~ elem(Plus) ~ thf_unitary_type ^^ {case typ ~ _ ~ r => +(typ,r)}
    )*/

  def thf_sequent: Parser[RepresentedFormula] = (
    thf_tuple ~ gentzen_arrow ~ thf_tuple           ^^ {case t1 ~ _ ~ t2 => SimpleSequent(t1,t2)}
      ||| elem(LeftParenthesis) ~> thf_sequent <~ elem(RightParenthesis)
    )

  def thf_tuple: Parser[List[E]] = repsep(thf_logic_formula, elem(Comma))

}