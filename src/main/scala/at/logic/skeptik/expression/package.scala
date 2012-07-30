package at.logic.skeptik
  
package object expression {
  import language.implicitConversions

  implicit def enrichString(s: String) = new RichString(s)
  
  //implicit def convertToVar(s: String) = Var(s, o)

}