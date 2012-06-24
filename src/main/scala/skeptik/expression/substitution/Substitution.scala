package skeptik.expression
package substitution

class Substitution(map: Map[Var,E]) {
  def apply(e: E) = {
    def rec(f:E,boundVars:Set[Var]):E = f match {
      case App(e1, e2) => App(rec(e1,boundVars),rec(e2,boundVars))
      case Abs(v,e) => Abs(v.copy, rec(e, boundVars + v))
      case v: Var if (boundVars contains v) => v.copy 
      case v: Var if (map contains v) => map(v).copy
      case v: Var => v.copy
    }
    rec(e, Set())
  }
}