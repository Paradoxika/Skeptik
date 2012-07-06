package skeptik.expression
package object formula {
  
  implicit def enrichFormula(e: E) = new RichFormula(e)

}