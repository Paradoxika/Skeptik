package ResK.algorithms

object generic {

  // "Abstract" trait to mark classes
  trait Duration { def duration:Long }

  class DurationMeasuredFunction1[-T,+R] (op: (T) => R)
  extends Function1[T,R] with Duration
  {
    var duration:Long = 0
    def apply(x:T) = {
      val begin = java.lang.System.currentTimeMillis
      val ret = op(x)
      duration = java.lang.System.currentTimeMillis - begin
      ret
    }
  }
  object DurationMeasuredFunction1 {
    def apply[T,R](op: (T) => R) = new DurationMeasuredFunction1(op)
  }

}
