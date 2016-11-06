package at.logic.skeptik.algorithm.compressor.FOSplit

import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.{App, E, Var}

/**
  * This trait implements the equality relation
  * between two literals in First-Order logic.
  */
trait AbstractEquality extends FOSplit {
  def equalLiterals(selectedLiteral: E, nodeLiteral: E): Boolean
}

/**
  * This equality is used when we consider that two literals are equal if they have the same name
  * For example, the following literals would be considered equal: P(X), P(a), P(b). (X is a variable,
  * a and b are constante). P is the "name" of the three literals
  */
trait NameEquality extends AbstractEquality {
  def equalLiterals(selectedLiteral: E, nodeLiteral: E): Boolean =
    (selectedLiteral, nodeLiteral) match {
      case (Atom(Var(name1,_), _), Atom(Var(name2,_), _)) => name1 == name2
      case (App(function,_), x)                           => equalLiterals(function,x)
      case (x, App(function,_))                           => equalLiterals(x,function)
      case (Var(name1,_),Var(name2,_))                    => name1 == name2
      case (Atom(Var(name1,_), _),          _           ) => false
      case _                                              => throw new Exception("The literal is not an instance of an Atom\nLiterals: " + selectedLiteral.toString + ", " + nodeLiteral.toString)
    }
}

trait AlphaEquivalenceAsEquality extends AbstractEquality {
  def equalLiterals(selectedLiteral: E, nodeLiteral: E): Boolean =
    (FOSplittingUtils.isMoreGeneralOrEqual(selectedLiteral,nodeLiteral,this.variables)
    && FOSplittingUtils.isMoreGeneralOrEqual(nodeLiteral,selectedLiteral,this.variables))


}

