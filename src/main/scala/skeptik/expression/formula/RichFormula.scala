package skeptik.expression
package formula

class RichFormula protected[formula] (e: E) {
  def implies(that: E) = Imp(e, that) 
  def →(that: E) = implies(that)

  def and(that: E) = And(e, that) 
  def ∧(that: E) = and(that)
 
  def or(that: E) = Or(e, that) 
  def ∨(that: E) = or(that) 
}