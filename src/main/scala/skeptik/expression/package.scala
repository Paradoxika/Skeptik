package skeptik
  
package object expression {

  implicit def enrichString(s: String) = new RichString(s)
  
  //implicit def convertToVar(s: String) = Var(s, o)

}