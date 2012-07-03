package skeptik.util

object unicode {
  def unicodeOrElse(unicode: String, alternative: String) = 
    if (System.getProperty("file.encoding") == "UTF-8") unicode
    else alternative
}

object debug {
  def debug(s: Any)(implicit i:Int) = {
    //println(((1 to i).toList.map(x => "    ") :\ "")(_+_) + s)
  }
}

object time {
  import actors.Futures.{awaitAll, future}
  
  def timeout[R](time: Long)(f: => R): Option[R] = awaitAll(time, future {f}).head.asInstanceOf[Option[R]]

  def timeout[R](time: Long, default: R)(f: => R): R = timeout(time)(f).getOrElse(default)
  
  case class Timed[+R](result:R, time: Double)
  def timed[R](f: => R): Timed[R] = {
    System.gc()
    val now = System.nanoTime
    val result = f
    val time = (System.nanoTime - now) / 1000 // in microseconds
    Timed(result, time)
  }
  def timed[R](repetitions: Int)(f: => R): Timed[R] = {
    val Timed(r,t) = timed { f }
    val averageTime = (for (i <- 1 to repetitions - 1) yield timed(f).time).foldLeft(t)(_+_) / repetitions
    Timed(r, averageTime.floor)
  }
}

object io {
  import java.io.{File,PrintWriter}
  
  def printToFile(f: File)(op: PrintWriter => Unit) {
    val p = new PrintWriter(f)
    try { op(p) } finally { p.close() }
  }
  def printToFile(f: File, s: String):Unit = printToFile(f)(p => p.println(s))
}

    
