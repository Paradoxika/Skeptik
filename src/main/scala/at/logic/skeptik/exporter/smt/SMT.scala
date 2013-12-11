package at.logic.skeptik.exporter
package smt

import java.io.FileWriter

class SMTFileExporter(filename: String) extends Exporter with ExpressionE with SequentE with ProofE {
  val w = new FileWriter(filename)
  def write(s: Array[Char], off: Int, len: Int) = w.write(s,off,len)
  def close() = w.close()
  def flush() = w.flush()
}
