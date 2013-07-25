package at.logic.skeptik.proof

case class Measurements(length:Int, core:Int, height: Int) {
  override def toString = "length = " + length + " , " +
                          "core = " + core + " , " +
                          "height = " + height + "  "
  
  def toSeq = Seq(length, core, height)
}
