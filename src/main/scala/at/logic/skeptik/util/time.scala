package at.logic.skeptik.util

object time {
  // ToDo: Use Duration for time

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
    
