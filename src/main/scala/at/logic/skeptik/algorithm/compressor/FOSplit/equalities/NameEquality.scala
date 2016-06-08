package at.logic.skeptik.algorithm.compressor.FOSplit.equalities

import at.logic.skeptik.expression.formula.Atom
import at.logic.skeptik.expression.{E, Var}

/**
  * This equality is used when we consider that two literals are equal if they have the same name
  * For example, the following literals would be considered equal: P(X), P(a), P(b). (X is a variable,
  * a and b are constante). P is the "name" of the three literals
  */
trait NameEquality {
  def equalLiterals(selectedLiteral: E, nodeLiteral: E): Boolean =
    (selectedLiteral, nodeLiteral) match {
      case (Atom(name1, _), Atom(name2, _)) => name1 == name2
      case (Atom(name1, _),      _       )  => false
      case _                                => throw new Exception("The literal is not an instance of an Atom\nLiterals: " + selectedLiteral.toString + ", " + nodeLiteral.toString)
    }
}
