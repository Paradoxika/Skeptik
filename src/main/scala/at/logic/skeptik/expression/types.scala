package at.logic.skeptik.expression

import at.logic.skeptik.util.unicode._

abstract class T {
  def ->(t:T) = Arrow(this,t)
  def logicalSize: Int
}
trait Atomic {
  def logicalSize = 1
}
case object i extends T with Atomic
case object o extends T with Atomic
final case class AtomicType(name: String) extends T with Atomic {
  override def toString = name
}
final case class Arrow(t1:T, t2:T) extends T {
  override def toString = "(" + t1 + unicodeOrElse("\u2192","->") + t2 + ")"
  def logicalSize = t1.logicalSize + t2.logicalSize + 1
}
