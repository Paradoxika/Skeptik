package at.logic.skeptik.algorithm.congruence

trait earlyRes {
  def resolveEarly: Boolean = true
}

trait lazyRes {
  def resolveEarly: Boolean = false
}