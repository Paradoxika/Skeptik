package at.logic.skeptik.exporter
package smt

import java.io.FileWriter

class FileExporter(filename: String) extends BasicFileExporter(filename) with ExpressionE with SequentE with ProofE {
  def extension = "smt2"
}
