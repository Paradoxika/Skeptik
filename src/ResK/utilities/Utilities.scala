package ResK.utilities

object debug {
  def apply(condition: Boolean, s: Any) = if (condition) println(s)
  def apply(s: Any) = println(s)
}

object prettyPrinting {
  def listToCSVString[X](l:List[X]) = l match {
    case Nil => ""
    case _ => (l.head.toString /: l.tail)((x,y)=> "" + x + "," + y)
  }
}
