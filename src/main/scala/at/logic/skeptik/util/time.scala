package at.logic.skeptik.util

import scala.actors.Futures.{awaitAll, future}

object time {
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
    
