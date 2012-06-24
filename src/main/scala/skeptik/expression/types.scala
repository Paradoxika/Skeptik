package skeptik.expression

import skeptik.util.unicode._

sealed abstract class T {
  def ->(t:T) = arrow(this,t)
  def size: Int
}
trait Atomic {
  def size = 1
}
case object i extends T with Atomic
case object o extends T with Atomic
final case class arrow(t1:T, t2:T) extends T {
  override def toString = "(" + t1 + unicodeOrElse("\u2192","->") + t2 + ")"
  def size = t1.size + t2.size + 1
}
