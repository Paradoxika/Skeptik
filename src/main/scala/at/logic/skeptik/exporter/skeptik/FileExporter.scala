package at.logic.skeptik.exporter
package skeptik

import java.io.FileWriter

class FileExporter(filename: String, val deletionInfo: Boolean = false) extends BasicFileExporter(filename) with ExpressionE with SequentE with ProofE {
  def extension = if (deletionInfo) "sd" else "s"
}
