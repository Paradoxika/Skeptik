package at.logic.skeptik.exporter

import java.io.FileWriter

abstract class BasicFileExporter(filename: String) extends Exporter {
  def extension: String
  val w = new FileWriter(filename + "." + extension)
  def write(s: Array[Char], off: Int, len: Int) = w.write(s,off,len)
  def close() = w.close()
  def flush() = w.flush()
}