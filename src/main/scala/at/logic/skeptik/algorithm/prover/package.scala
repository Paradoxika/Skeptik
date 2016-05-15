package at.logic.skeptik.algorithm

import at.logic.skeptik.expression.Var
import at.logic.skeptik.judgment.immutable.{UnitSequent, VarSeqSequent}

import scala.language.implicitConversions

/**
  * @author Daniyar Itegulov
  */
package object prover {
  type Clause = VarSeqSequent
  type Literal = UnitSequent

  object Clause {
    def apply(a: Var*)(b: Var*) = VarSeqSequent(a:_*)(b:_*)
    def empty = VarSeqSequent()()
  }

  implicit def varToLit(variable: Var): Literal = new Literal(variable, false)
}
