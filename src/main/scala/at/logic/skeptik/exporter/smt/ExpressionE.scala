package at.logic.skeptik.exporter
package smt

import at.logic.skeptik.expression.{E,Var,Abs,App,AppRec}
import at.logic.skeptik.expression.formula._


trait ExpressionE extends Exporter {
  def write(e: E): Unit = e match {
    case Var(n,_) => {
      if (n == andS) write("and")
      else if (n == orS) write("or")
      else if (n == negS) write("not")
      else if (n == allS) write("all")
      else if (n == exS) write("all")
      else write(n)
    }
    case App(App(Var(p,_), e1), e2) if p == eqS => {
      write("(= ")
      write(e1)
      write(" ")
      write(e2)
      write(")")
    }
    case AppRec(f,args) => {
      write("(")
      write(f)
      for (a <- args) {
        write(" ")
        write(a)
      }
      write(")")
    }
    case _ => write(e.toString)
  }
}