package at.logic.skeptik.expression

class RichString protected[expression] (s: String) {
  def ^(t: T) = Var(s, t) 
}

