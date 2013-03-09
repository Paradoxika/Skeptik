package at.logic.skeptik

import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.exporter.ProofExporterVeriT
import at.logic.skeptik.parser.ProofParserSkeptik
import at.logic.skeptik.exporter.ProofExporterSkeptik
import at.logic.skeptik.algorithm.compressor.Algorithms

object ProofCompressionCLI {

  case class Config(input: String = "",
                    algorithm: String = "RPI", 
                    output: String = "")                
      
  def unknownFormat(filename: String) = "Unknown format for " + filename + ". Supported formats are '.smt2' and '.skeptik'"                 
                    
  def main(args: Array[String]): Unit = {  
    val parser = new scopt.immutable.OptionParser[Config]("compress", "\n\nSkeptik's Command Line Interface for Proof Compression\n\n") { def options = Seq(
      opt("a", "algorithm", "the algorithm to be used for compressing the proof") { (v: String, c: Config) => c.copy(algorithm = v) },
      opt("o", "output", "<output file>", "file to store the compressed proof") { (v: String, c: Config) => c.copy(output = v) },
      arg("<input file>", "file containing the proof to be compressed") { (v: String, c: Config) => c.copy(input = v) }
    ) }
    // parser.parse returns Option[C]
    parser.parse(args, Config()) map { config =>
      
      println("Reading proof...")
      val proof = ("""\.[^\.]+$""".r findFirstIn config.input) match {
        case Some(".smt2")  => ProofParserVeriT.read(config.input)
        case Some(".skeptik")  => ProofParserSkeptik.read(config.input)
        case _ => throw new Exception(unknownFormat(config.input))
      }
      
      println("Compressing proof...")
      val compressedProof = Algorithms.get(config.algorithm)(proof)
      
      if (config.output != "") {
        println("Writing compressed proof...")
        ("""\.[^\.]+$""".r findFirstIn config.output) match {
          case Some(".smt2") => ProofExporterVeriT.write(compressedProof, config.output)
          case Some(".skeptik") => ProofExporterSkeptik.write(compressedProof, config.output)
          case _ => throw new Exception(unknownFormat(config.output))
        }
        
      }
       
      
    } getOrElse { } // arguments are bad, usage message will have been displayed
  }
}
