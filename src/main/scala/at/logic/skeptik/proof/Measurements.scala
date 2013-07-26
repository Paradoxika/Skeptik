package at.logic.skeptik.proof

case class Measurements(length:Int, core:Int, height: Int) {
  override def toString = "length = " + length + " , " +
                          "core = " + core + " , " +
                          "height = " + height + "  "
  
  def zipWith[B](that: Measurements)(op: (Int,Int)=>B) = {
    Seq(op(length,that.length),op(core,that.core),op(height,that.height))
  }
                          
  def toSeq = Seq(length, core, height)
}
