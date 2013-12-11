package at.logic.skeptik.exporter
package smt

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.judgment.Sequent


trait SequentE extends ExpressionE {
  def write(s: Sequent): Unit = {
    val disjuncts = (s.ant.map(f => neg(f)).view ++ s.suc)
    write("(")
    if (!disjuncts.isEmpty) {
      write(disjuncts.head)
      for (f <- disjuncts.tail) { 
        write(" ")
        write(f)       
      }
    } 
    write(")")
  }
}