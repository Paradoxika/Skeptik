package ResK.utilities

object debug {
  def apply(condition: Boolean, s: Any) = if (condition) println(s)
  def apply(s: Any) = println(s)
}
