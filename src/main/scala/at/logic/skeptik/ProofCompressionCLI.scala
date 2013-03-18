package at.logic.skeptik

import at.logic.skeptik.parser.{ProofParser,ProofParserVeriT,ProofParserSkeptik}
import at.logic.skeptik.exporter.{ProofExporterVeriT,ProofExporterSkeptik}
import at.logic.skeptik.algorithm.compressor.Algorithms
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.{Proof, ProofNode}
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.time._
import at.logic.skeptik.util.pretty._

object ProofCompressionCLI {

  case class Config(input: String = "",
                    algorithm: String = "", 
                    output: String = "")                
      
  def unknownFormat(filename: String) = "Unknown proof format for " + filename + ". Supported formats are '.smt2' and '.skeptik'"                 
  
  def completedIn(t: Double) = " (completed in " + Math.round(t) + "ms)"       
  
  def unknownAlgorithm(a: String) = "Algorithm " + a + " is unknown."
  
  def main(args: Array[String]): Unit = {  
    val parser = new scopt.immutable.OptionParser[Config]("compress", "\n\nSkeptik's Command Line Interface for Proof Compression\n\n") { def options = Seq(
      opt("a", "algorithm", "the algorithm to be used for compressing the proof") { (v: String, c: Config) => c.copy(algorithm = v) },
      opt("o", "output", "<output file>", "file to store the compressed proof") { (v: String, c: Config) => c.copy(output = v) },
      arg("<input file>", "file containing the proof to be compressed") { (v: String, c: Config) => c.copy(input = v) }
    ) }
    // parser.parse returns Option[C]
    parser.parse(args, Config()) map { config =>
      
      println()
      
      // ToDo: should not throw exception when the error is due to the user.
      
      // Reading the proof
      print("Reading and checking proof...")
      val proofParser = ("""\.[^\.]+$""".r findFirstIn config.input) match {
        case Some(".smt2")  => ProofParserVeriT
        case Some(".skeptik")  => ProofParserSkeptik
        case _ => throw new Exception(unknownFormat(config.input))
      }
      import at.logic.skeptik.proof.sequent.SequentProofNode
      import at.logic.skeptik.judgment.Sequent
      val Timed(proof, tRead) = timed { proofParser.read(config.input) }   
      println(completedIn(tRead))
      
      
      // Compressing the proof
      val outputProof = if (config.algorithm != "") {
                          print("Compressing proof...")
                          val algorithm = Algorithms.get(config.algorithm)
                          val Timed(p, t) = timed { algorithm(proof) }
                          println(completedIn(t))
                          p
                        }
                        else proof
                        
      
      // Writing the compressed proof
      if (config.output != "") {
        print("Writing compressed proof...")
        val proofWriter = ("""\.[^\.]+$""".r findFirstIn config.output) match {
          case Some(".smt2") => ProofExporterVeriT
          case Some(".skeptik") => ProofExporterSkeptik
          case _ => throw new Exception(unknownFormat(config.output))
        }
        val Timed(_,t) = timed { proofWriter.write(outputProof, config.output) }
        println(completedIn(t))
      }
      
      // Displaying proof measurements
      println()
      println("Proof measurements:")     
      val header = Seq("Proof", "Length", "Width", "Height")
      val mIProof = measure(proof)
      val input = Seq("input") ++ mIProof.toSeq
      val outputRows = if (! (outputProof eq proof)) {
        val mOProof = measure(outputProof)
        val compressions = (mIProof.toSeq zip mOProof.toSeq) map {case (i,o) => 
                             (Math.round(1000.0*o/i)/10.0) + "%"
                           }  
        Seq(Seq("output") ++ ((mOProof.toSeq zip compressions) map {case (o,c) => o + " (" + c + ")"})) 
      }
      else Seq()
      
      val data = Seq(header, input) ++ outputRows
                  
      println()
      print(prettyTable(data))
      
      print(
""" 
  where:           
    Length = number of inferences in the proof
    Width = number of axioms in the proof
    Height = length of longest path from leaf to root
          
""")
                    
    } getOrElse { // arguments are bad 
      
    } 
  }
}
