package at.logic.skeptik.proof

case class Measurements(length:Int, width:Int, height: Int) {
  override def toString = "length = " + length + " , " +
                          "width = " + width + " , " +
                          "height = " + height + "  "
  
  def toSeq = Seq(length, width, height)
}
