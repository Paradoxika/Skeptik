package at.logic.skeptik.expression
package substitution

//ToDo: (B) Take care of bound variable renaming, in order to avoid variable capture. 
abstract class AbstractSubstitution {
  protected def m: Map[Var,E]
  def apply(e: E) = {
    def rec(f:E,boundVars:Set[Var]):E = f match {
      case App(e1, e2) => App(rec(e1,boundVars),rec(e2,boundVars))
      case Abs(v,e) => Abs(v.copy, rec(e, boundVars + v))
      case v: Var if (boundVars contains v) => v.copy 
      case v: Var if (m contains v) => m(v).copy
      case v: Var => v.copy
    }
    rec(e, Set())
  }
}