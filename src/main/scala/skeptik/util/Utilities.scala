package skeptik.util

//object debug {
//  def apply(condition: Boolean, s: Any) = if (condition) println(s)
//  def apply(s: Any) = println(s)
//}

object unicode {
  def unicodeOrElse(unicode: String, alternative: String) = 
    if (System.getProperty("file.encoding") == "UTF-8") unicode
    else alternative
}

object prettyPrinting {
  def listToCSVString[X](l:List[X]) = {
    l match {
      case Nil => ""
      case h::t => (h.toString /: t)((x,y)=> "" + x + "," + y)
    }
  }
}
