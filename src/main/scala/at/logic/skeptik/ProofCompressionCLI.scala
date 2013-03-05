package at.logic.skeptik

import java.io.FileReader
import at.logic.skeptik.parser.ProofParserVeriT

object ProofCompressionCLI {
  
  case class Config(input: String = "",
                      algorithm: String = "RPI", 
                      output: String = "")
                      
  def main(args: Array[String]): Unit = {
    
                      
    val parser = new scopt.immutable.OptionParser[Config]("sbt run", "\n\nSkeptik's Command Line Interface for Proof Compression\n\n") { def options = Seq(
      opt("a", "algorithm", "the algorithm to be used for compressing the proof") { (v: String, c: Config) => c.copy(algorithm = v) },
      arg("<input file>", "file containing the proof to be compressed") { (v: String, c: Config) => c.copy(input = v) },
      arg("<output file>", "file that will contain the compressed proof") { (v: String, c: Config) => c.copy(input = v) }
    ) }
    // parser.parse returns Option[C]
    parser.parse(args, Config()) map { config =>
      // read proof
      ("""\.[^\.]+$""".r findFirstIn config.input) match {
        case Some(".smt2")  => ProofParserVeriT.parse(new FileReader(config.input))
        case _ => throw new Exception("Unknown format for " + config.input)
      }
    } getOrElse { } // arguments are bad, usage message will have been displayed
  }
}
