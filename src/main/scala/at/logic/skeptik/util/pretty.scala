package at.logic.skeptik.util

import at.logic.skeptik.util.math._
import annotation.tailrec

object pretty {
  def blankString(length: Int): String = repString(" ", "", length)
  
  def mkStringMultiLine(c:Iterable[Any], leftMargin: Int, width: Int, sep: String) = {
    val margin = blankString(leftMargin)
    var counter = margin.length
    var paragraph = margin
    for (w <- c) {
      paragraph += w + sep
      counter += w.toString.length + sep.length
      if (counter > width) {
        paragraph += "\n" + margin
        counter = margin.length
      }
    }
    paragraph
  }
  
  
  def prettyTable[A](t: Seq[Seq[A]], sep: String = "   ", header: Boolean = true) = {
    val tTrans = t.transpose
    val widths: Seq[Seq[Int]] = t map {r => r map {e => e.toString.length}}
    val sepWidth = sep.length
    val columnWidths: Seq[Int] = {
      val widthsTrans = widths.transpose
      widthsTrans map {column => max(column, (x:Int) => x)}
    }
    val fixedWidthTableTrans: Seq[Seq[String]] = {
      for (columnWidthPair <- (tTrans zip columnWidths)) yield {
        val (column, width) = columnWidthPair
        column map {e => 
          val s = e.toString
          s + blankString(width - s.length)
        }
      }
    }
    val fixedWidthTable: Seq[Seq[String]] = fixedWidthTableTrans.transpose
    if (header) {
      val totalWidth = (0 /: columnWidths) {(w, e) => w + e + sepWidth}
      val horizontalBar = repString("=", "", totalWidth) + "\n"
      ((fixedWidthTable.head.mkString("", sep, "\n") + horizontalBar ) /: (fixedWidthTable.tail map { row => row.mkString("", sep, "\n") })) {_ + _}
    }
    else ("" /: (fixedWidthTable map { row => row.mkString("", sep, "\n") })) {_ + _}
  }
   
  @tailrec def repString(rep: String, s: String, length: Int): String = {
    if (length <= 0) s
    else repString(rep, s + rep, length - 1)
  }
}
    
