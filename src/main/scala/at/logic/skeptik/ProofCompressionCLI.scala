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
import scala.io.Source.fromFile

object ProofCompressionCLI {

  case class Config(inputs: Seq[String] = Seq(),
                    algorithms: Seq[String] = Seq(), 
                    outputformat: String = "",
                    csv: Boolean = false)                
    
  val supportedProofFormats = Seq("smt2", "skeptik")
  
  def unknownFormat(filename: String) = "Unknown proof format for " + filename + ". Supported formats are '.smt2' and '.skeptik'"                 
  
  def completedIn(t: Double) = " (completed in " + Math.round(t) + "ms)"       
  
  def unknownAlgorithm(a: String) = "Algorithm " + a + " is unknown."
  
  def main(args: Array[String]): Unit = {  
    val parser = new scopt.OptionParser[Config]("compress"){
      head("\nSkeptik's Command Line Interface for Proof Compression\n\n") 

      opt[String]('a', "algorithm") unbounded() action { (v, c) => 
        c.copy(algorithms = c.algorithms ++ Seq(v))
      } text("use <alg> to compress proofs") valueName("<alg>")
      
      opt[String]("algorithms") action { (v, c) => 
        c.copy(algorithms = c.algorithms ++ fromFile(v).getLines) 
      } text("use algorithms listed in <file>\n") valueName("<file>")
   
      note(
      """
        <alg> can be any of the following atomic algorithms:
      """ + 
      (for (a <- at.logic.skeptik.algorithm.compressor.algorithms) yield a._1).mkString(",  ") + "\n" + 
      """
        or a sequential composition denoted by '(alg1*alg2*...*algN)'
      """    
      )  
      
      opt[String]('o', "output") action { (v, c) => 
        c.copy(outputformat = v) 
      } validate { v =>
        if (supportedProofFormats contains v) success 
        else failure("unknown proof format: " + v)
      } text("use <format> to output compressed proofs") valueName("<format>")
 
      note(
      """
        <format> can be:
          smt2    - VeriT's proof format
          skeptik - Skeptik's proof format
      """
      )

      opt[Unit]("csv") action { (_, c) =>
        c.copy(csv = true) 
      } text("output statistics to a csv file\n")
      
      opt[String]('p', "proofs") action { (v, c) => 
        c.copy(inputs = c.inputs ++ fromFile(v).getLines) 
      } text("compress proofs from files listed in <file>\n") valueName("<file>")
      
      arg[String]("<proof-file>...") unbounded() optional() action { (v, c) =>
        c.copy(inputs = c.inputs ++ Seq(v)) 
      } text("compress proof from <proof-file>\n")
      
      help("help") text("print this usage text")
      
      note(
      """
      Example:
        The following command processes the proof 'eq_diamond9.smt2' using the
        algorithms 'RP' and the sequential composition of 'DAGify', 'RPI' and 'LU'.
        The compressed proofs are written using 'skeptik' proof format.
        And a csv file containing compression statistics is produced.
  
        compress -csv -a RP -a (DAGify*RPI*LU) -o skeptik examples/proofs/VeriT/eq_diamond9.smt2
  
      """)
    }
    // parser.parse returns Option[C]
    parser.parse(args, Config()) map { config =>
      
      println()
         
      if (config.inputs.isEmpty) parser.showUsage
      else {
        
        // measurement table initialized with its header only
        // rows with data for every input or output proof are added during execution 
        // and the table is displayed to the user at the end
        var measurementTable: Seq[Seq[Any]] = Seq(Seq("Proof", "Length", "Core", "Height")) 
        
        // convenient method for writing statistics in a csv file
        val csvWriter = if (config.csv) Some(new FileWriter(config.algorithms.mkString(",") + ".csv"))
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
          writeToCSV(proofName + ",\t")
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
        print(prettyTable(measurementTable))
        
        print(""" 
          where:           
            Length = number of inferences in the proof
            Core = number of axioms in the proof
            Height = length of longest path from leaf to root         
        """ + "\n")
      } // end of else of 'if (config.inputs.isEmpty)'
            
    } getOrElse { // arguments are bad 
     
    } 
  }
}
