package at.logic.skeptik.util

object math {
  def argMin[A](s: Traversable[A], size: A => Int) = {
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