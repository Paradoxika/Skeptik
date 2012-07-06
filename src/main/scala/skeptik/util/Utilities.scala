package skeptik.util

object unicode {
  def unicodeOrElse(unicode: String, alternative: String) = 
    if (System.getProperty("file.encoding") == "UTF-8") unicode
    else alternative
}

object debug {
  def debug(s: Any)(implicit i:Int) = {
    println(((1 to i).toList.map(x => "    ") :\ "")(_+_) + s)
  }
}

object argMin {
  def apply[A](s: Traversable[A], size: A => Int) = {
    def rec(t: Traversable[A]): (Option[A],Int) = t.toList match {
      case Nil => (None, Int.MaxValue)
      case h::tail => {
        val r @ (bestInTail,min) = rec(tail)
        val hSize = size(h)
        if (hSize < min) (Some(h), hSize)
        else r
      }
    }
    rec(s)._1
  }
  
}

object time {
  import actors.Futures.{awaitAll, future}
  
  def timeout[R](time: Long)(f: => R): Option[R] = awaitAll(time, future { f }).head.asInstanceOf[Option[R]]

  def timeout[R](time: Long, default: R)(f: => R): R = timeout(time)(f).getOrElse(default)
  
  case class Timed[+R](result:R, time: Double)
  def timed[R](f: => R): Timed[R] = {
    System.gc()
    val now = System.nanoTime
    val result = f
    val time = (System.nanoTime.toDouble - now) / 1000000 // in milliseconds
    Timed(result, time)
  }
  def timed[R](repetitions: Int)(f: => R): Timed[R] = {
    val Timed(r,t) = timed { f }
    val averageTime = (for (i <- 1 to repetitions - 1) yield timed(f).time).foldLeft(t)(_+_) / repetitions
    Timed(r, averageTime)
  }
}
    
