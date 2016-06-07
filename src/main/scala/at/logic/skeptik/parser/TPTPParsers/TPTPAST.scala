package at.logic.skeptik.parser.TPTPParsers

import at.logic.skeptik.expression.E

/**
  * TPTP Syntax representation.
  *
  * @author Ezequiel Postan
  * @since 24.05.2016
  */
object TPTPAST {

  /*
   * TODO: Think about let expressions
   */
  sealed abstract class RepresentedFormula
  case class SimpleSequent(ant : Seq[E], suc : Seq[E]) extends RepresentedFormula
  case class SimpleFormula(formula : E)                extends RepresentedFormula

  type Name        = String
  type Language    = String
  type FormulaRole = String
  type Annotations = Option[(Source, List[GeneralTerm])]

  abstract class TPTPDirective
  case class IncludeDirective(fileName : String, selectedFormulas : List[Name])       extends TPTPDirective
  case class AnnotatedFormula(language: Language, name: Name, role: FormulaRole,
                              formula: RepresentedFormula , annotations: Annotations) extends TPTPDirective


  // General purpose things
  type Source = GeneralTerm

  // Non-logical data (GeneralTerm, General data)
  sealed case class GeneralTerm(term: List[Either[GeneralData, List[GeneralTerm]]])

  sealed abstract class GeneralData
  case class GWord(gWord: String)                         extends GeneralData
  case class GFunc(name: String, args: List[GeneralTerm]) extends GeneralData
  case class GVar(gVar: String)                           extends GeneralData
  case class GNumber(gNumber: String)                     extends GeneralData
  case class GDistinct(data: String)                      extends GeneralData
  case class GFormulaData(formulaData: FormulaData)       extends GeneralData

  class FormulaData(val language: Language)
  case class GFormulaDataTerm(override val language: Language, term : E) extends FormulaData(language)
  case class GFormulaDataFormula(override val language: Language,
                                 formula : RepresentedFormula)           extends FormulaData(language)
}
