package at.logic.skeptik

import at.logic.skeptik.parser.{ProofParser,ProofParserVeriT,ProofParserSkeptik,AlgorithmParser}
import at.logic.skeptik.exporter.{ProofExporterVeriT,ProofExporterSkeptik}
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.time._
import at.logic.skeptik.util.pretty._

import java.io.FileWriter

object ProofCompressionCLI {

  case class Config(inputs: Seq[String] = Seq(),
                    algorithms: Seq[String] = Seq(), 
                    outputformat: String = "",
                    csv: Boolean = false)                
      
  def unknownFormat(filename: String) = "Unknown proof format for " + filename + ". Supported formats are '.smt2' and '.skeptik'"                 
  
  def completedIn(t: Double) = " (completed in " + Math.round(t) + "ms)"       
  
  def unknownAlgorithm(a: String) = "Algorithm " + a + " is unknown."
  
  def main(args: Array[String]): Unit = {  
    val parser = new scopt.immutable.OptionParser[Config]("Skeptik's Command Line Interface for Proof Compression", "\n\n") { def options = Seq(
      opt("a", "algorithms", "<algorithms>", "the algorithms to be used for compressing the proof") { 
        (v: String, c: Config) => c.copy(algorithms = v.split(",")) 
      },
      opt("o", "outputformat", "<output format>", "proof format to be used for the compressed proofs") { 
        (v: String, c: Config) => c.copy(outputformat = v) 
      },
      flag("csv", "csv", "activates output of proof compression statistics to a csv file") { 
        (c: Config) => c.copy(csv = true) 
      },
      arg("<input files>", "comma-separated filenames of the files containing the proofs to be compressed") { 
        (v: String, c: Config) => c.copy(inputs = v.split(",")) }
    ) }
    // parser.parse returns Option[C]
    parser.parse(args, Config()) map { config =>
      
      println()
        
      // measurement table initialized with its header only
      // rows with data for every input or output proof are added during execution 
      // and the table is displayed to the user at the end
      var measurementTable: Seq[Seq[Any]] = Seq(Seq("Proof", "Length", "Width", "Height")) 
      
      // convenient method for writing compression statistics in a csv file
      val csvWriter = if (config.csv) Some(new FileWriter(config.algorithms.mkString("-") + ".csv"))
                      else None
      def writeToCSV(s: String) = for (w <- csvWriter) w.write(s,0,s.length)
      
      for (filename <- config.inputs) {
        // Reading the proof
        print("Reading and checking proof '"+ filename +"' ...")
        val proofFormat = ("""\.[^\.]+$""".r findFirstIn filename) getOrElse { throw new Exception(unknownFormat(filename)) }
        val proofName = filename.split(proofFormat)(0) // filename without extension
        val proofParser = proofFormat match {
          case ".smt2"  => ProofParserVeriT
          case ".skeptik"  => ProofParserSkeptik
        }
        val Timed(proof, tRead) = timed { proofParser.read(filename) }   
        println(completedIn(tRead))
        
        // Measuring the input Proof
        print("Measuring '"+ proofName +"' ...")
        val Timed(mIProof,tMIProof) = timed { measure(proof) }
        println(completedIn(tMIProof))
        
        // Adding measurements to measurement table
        val inputRow = (Seq(proofName) ++ mIProof.toSeq)
        measurementTable = measurementTable ++ Seq(inputRow)
        
        // Adding measurements to csv file
        writeToCSV(proofName + "\t,")
        writeToCSV(mIProof.toSeq.mkString("\t",",\t", ","))
        
        
        
        val writeProof =  {
          config.outputformat match {
            case "smt2" => (p: Proof[N], name: String) => ProofExporterVeriT.write(p, name)
            case "skeptik" => (p: Proof[N], name: String) => ProofExporterSkeptik.write(p, name)
            case "" =>  (p: Proof[N], name: String) => { }
          }
        }
        
        // Compressing the proof
        for (a <- config.algorithms) yield {
          val algorithm = AlgorithmParser.parse(a)
          print("Compressing with algorithm: " + a + "...")
          val Timed(p, t) = timed { algorithm(proof) }
          println(completedIn(t))
          
          val oProofName = proofName + "-" + a
          print("Writing compressed proof '" + oProofName + "'...")
          val Timed(_,w) = timed { writeProof(p, oProofName) }
          println(completedIn(w))
          
          print("Measuring '"+ oProofName +"' ...")
          val Timed(mOProof,tMOProof) = timed { measure(p) }
          println(completedIn(tMOProof))
          
          // Adding measurements to csv file
          writeToCSV(mOProof.toSeq.mkString("\t",",\t", ","))
          
          // Adding measurements to measurement table
          val outputRow = {
            val compressions = (mIProof.toSeq zip mOProof.toSeq) map { case (i,o) => 
              (Math.round(1000.0*o/i)/10.0) + "%"
            }  
            Seq(oProofName) ++ ((mOProof.toSeq zip compressions) map {case (o,c) => o + " (" + c + ")"}) 
          }
          measurementTable ++= Seq(outputRow)
        }            
         
        writeToCSV("\n")
      } // end of 'for (filename <- config.inputs)'
                           
      for (w <- csvWriter) w.close()
      
      // Displaying proof measurements
      println()
      println("Proof measurements:")     
      println()
      print(prettyTable(measurementTable))
      
      print(
""" 
  where:           
    Length = number of inferences in the proof
    Width = number of axioms in the proof
    Height = length of longest path from leaf to root
          
""")
                    
    } getOrElse { // arguments are bad 
      print(
"""Simple example: the following command will run the proof 
compression algorithm 'RecyclePivotsWithIntersection' 
on the proof 'eq_diamond8.smt2' (written in VeriT's proof format) 
and write the compressed proof in 'eq_diamond8-RPI.skeptik' 
(using Skeptik's proof format):

    compress -a RPI -o skeptik examples/proofs/VeriT/eq_diamond8.smt2
    
Available atomic algorithms:
  """ + (for (a <- at.logic.skeptik.algorithm.compressor.algorithms) yield a._1).mkString("\n  ") + "\n\n" +
"""
Algorithms can be sequentially composed. 
In the following command, the algorithms 
'LU', 'RPI' and 'DAGify' will be executed 
one after the other in this order:
    
    compress -a (DAGify.RPI.LU) examples/proofs/VeriT/eq_diamond8.smt2  
  
  
To experiment and compare several algorithms, 
they should be separated by commas. 
The following command executes '(RPI.LU)', '(LU.RPI)' and 'RP',
and outputs the results to 'eq_diamond8-(RPI.LU).smt2',
'eq_diamond8-(LU.RPI).smt2' and 'eq_diamond8-RP.smt2'
using VeriT's proof format:
  
    compress -a (RPI.LU),(LU.RPI),RP -o smt2 examples/proofs/VeriT/eq_diamond8.smt2
  
"""
      )      
    } 
  }
}
