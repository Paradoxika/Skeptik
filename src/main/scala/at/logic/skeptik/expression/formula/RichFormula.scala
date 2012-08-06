package at.logic.skeptik.expression
package formula

class RichFormula protected[formula] (e: E) {
  def implies(that: E) = Imp(e, that) 
  def →(that: E) = implies(that)

  def and(that: E) = And(e, that) 
  def ∧(that: E) = and(that)
 
  def or(that: E) = Or(e, that) 
  def ∨(that: E) = or(that) 
  
  // Unfortunately, the following doesn't work,
  // because Scala accepts only !, ~, + and - as prefix unary operators
  //def unary_neg = Neg(e) 
  //def unary_¬ = unary_neg
}