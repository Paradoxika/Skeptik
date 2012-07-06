package skeptik.expression
package formula

class RichFormula protected[formula] (e: E) {
  def imp(that: E) = Imp(e, that) 
  def →(that: E) = imp(that)
  def implies(that: E) = imp(that)
}