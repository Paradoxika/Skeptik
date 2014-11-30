package at.logic.skeptik.exporter
package smt

import java.io.FileWriter

class FileExporter(filename: String, val avoidChains: Boolean = false, val omitConclusion: Boolean = false) extends BasicFileExporter(filename) with ExpressionE with SequentE with ProofE {
  def extension = {
    if (!avoidChains && !omitConclusion) "smt2"
    else "smt" + (if (avoidChains) "b" else "") + (if (omitConclusion) "c" else "")    
  }
}
