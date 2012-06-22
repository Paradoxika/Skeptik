package skeptik.util

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


object debug {
  def debug(s: Any)(implicit i:Int) = {
    //println(((1 to i).toList.map(x => "    ") :\ "")(_+_) + s)
  }
}
    
