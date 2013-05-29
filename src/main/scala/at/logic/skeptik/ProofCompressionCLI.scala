package at.logic.skeptik

import at.logic.skeptik.parser.{ProofParser,ProofParserVeriT,ProofParserSkeptik,AlgorithmParser}
import at.logic.skeptik.exporter.{ProofExporterVeriT,ProofExporterSkeptik}
import at.logic.skeptik.algorithm.compressor.algorithms
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.time._
import at.logic.skeptik.util.pretty._

object ProofCompressionCLI {

  case class Config(input: String = "",
                    algorithms: String = "", 
                    output: String = "")                
      
  def unknownFormat(filename: String) = "Unknown proof format for " + filename + ". Supported formats are '.smt2' and '.skeptik'"                 
  
  def completedIn(t: Double) = " (completed in " + Math.round(t) + "ms)"       
  
  def unknownAlgorithm(a: String) = "Algorithm " + a + " is unknown."
  
  def main(args: Array[String]): Unit = {  
    val parser = new scopt.immutable.OptionParser[Config]("Skeptik's Command Line Interface for Proof Compression", "\n\n") { def options = Seq(
      opt("a", "algorithms", "<algorithms>", "the algorithms to be used for compressing the proof") { (v: String, c: Config) => c.copy(algorithms = v) },
      opt("o", "output format", "<output format>", "proof format to be used for the compressed proofs") { (v: String, c: Config) => c.copy(output = v) },
      arg("<input file>", "file containing the proof to be compressed") { (v: String, c: Config) => c.copy(input = v) }
    ) }
    // parser.parse returns Option[C]
    parser.parse(args, Config()) map { config =>
      
      println()
      
      // Reading the proof
      print("Reading and checking proof '"+ config.input +"' ...")
      val proofFormat = ("""\.[^\.]+$""".r findFirstIn config.input) getOrElse { throw new Exception(unknownFormat(config.input)) }
      val proofName = config.input.split(proofFormat)(0)
      val proofParser = proofFormat match {
        case ".smt2"  => ProofParserVeriT
        case ".skeptik"  => ProofParserSkeptik
      }
      val Timed(proof, tRead) = timed { proofParser.read(config.input) }   
      println(completedIn(tRead))
      
      
      val writeProof =  {
        config.output match {
          case "smt2" => (p: Proof[N]) => ProofExporterVeriT.write(p, proofName)
          case "skeptik" => (p: Proof[N]) => ProofExporterSkeptik.write(p, proofName)
          case "" =>  (p: Proof[N]) => { }
        }
      }
      
      // Compressing the proof
      val algorithmNames = config.algorithms.split(",")
      val outputProofs = {
        val algorithms = AlgorithmParser.parseMany(config.algorithms)
        for ((a,n) <- algorithms zip algorithmNames) yield {
          print("Compressing with algorithm: " + n + "...")
          val Timed(p, t) = timed { a(proof) }
          println(completedIn(t))
          print("Writing compressed proof...")
          val Timed(_,w) = timed { writeProof(p) }
          println(completedIn(w))
          p  
        }            
      }
                         
      
      // Displaying proof measurements
      println()
      println("Proof measurements:")     
      val header = Seq("Proof", "Length", "Width", "Height")
      val mIProof = measure(proof)
      val input = Seq(proofName) ++ mIProof.toSeq
      val outputRows = for ((p,n) <- outputProofs zip algorithmNames) yield {
        val mOProof = measure(p)
        val compressions = (mIProof.toSeq zip mOProof.toSeq) map { case (i,o) => 
                             (Math.round(1000.0*o/i)/10.0) + "%"
                           }  
        Seq(proofName + "-" + n) ++ ((mOProof.toSeq zip compressions) map {case (o,c) => o + " (" + c + ")"}) 
      }
      
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
      print(
"""Example: The following command will run the proof 
  compression algorithm 'RecyclePivotsWithIntersection' 
  on the proof 'eq_diamond8.smt2' (written in VeriT's proof format) 
  and write the compressed proof in 'output.skeptik' 
  (using Skeptik's proof format):

    compress examples/proofs/VeriT/eq_diamond8.smt2 --algorithm RPI --output output.skeptik
    
Available algorithms:
  """ + (for (a <- algorithms) yield a._1).mkString("\n  ") + "\n\n"    
      )      
    } 
  }
}
