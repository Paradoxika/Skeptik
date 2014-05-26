package at.logic.skeptik.congruence

trait earlyRes {
  def resolveEarly: Boolean = true
}

trait lazyRes {
  def resolveEarly: Boolean = false
}