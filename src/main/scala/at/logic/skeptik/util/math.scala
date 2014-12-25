package at.logic.skeptik.util

object math {
  def argMax[A](s: Traversable[A], size: A => Int) = genericMinMax(s,size,Int.MinValue, _ > _)._1
  def argMin[A](s: Traversable[A], size: A => Int) = genericMinMax(s,size,Int.MaxValue, _ < _)._1
  
  def max[A](s: Traversable[A], size: A => Int, default: Int = Int.MinValue) = genericMinMax(s,size,default, _ > _)._2
  def min[A](s: Traversable[A], size: A => Int, default: Int = Int.MaxValue) = genericMinMax(s,size,default, _ < _)._2
  
  def genericMinMax[A](s: Traversable[A], size: A => Int, default: Int, compare: (Int,Int) => Boolean ) = {
    def rec(t: Traversable[A]): (Option[A],Int) = t.toList match {
      case Nil => (None, default)
      case h::tail => {
        val r @ (bestInTail,max) = rec(tail)
        val hSize = size(h)
        if (compare(hSize,max)) (Some(h), hSize)
        else r
      }
    }
    rec(s)
  }  
}