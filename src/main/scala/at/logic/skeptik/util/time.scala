package at.logic.skeptik.util

import scala.language.postfixOps
import scala.concurrent._
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global

object time {
  // ToDo: Use Duration for time

  def timeout[R](time: Long)(f: => R): Option[R] = 
    try { Some(Await.result(Future { f }, time millis)) } catch {
      case e: TimeoutException => None
    }

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
    
