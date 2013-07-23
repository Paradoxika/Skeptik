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
import java.io.File
import java.io.BufferedReader
import java.io.FileReader
import scala.io.Source.fromFile


object ProofCompressionCLI {

  case class Config(inputs: Seq[String] = Seq(),
                    algorithms: Seq[String] = Seq(), 
                    outputformat: String = "",
                    csv: Boolean = false)                
      
  def unknownFormat(filename: String) = "Unknown proof format for " + filename + ". Supported formats are '.smt2' and '.skeptik'"                 
  
  def completedIn(t: Double) = " (completed in " + Math.round(t) + "ms)"       
  
  def unknownAlgorithm(a: String) = "Algorithm " + a + " is unknown."
  
  def main(args: Array[String]): Unit = {  
    val parser = new scopt.OptionParser[Config]("compress"){
      head("- Skeptik's Command Line Interface for Proof Compression") 

      opt[String]('a', "algorithms") action { (v, c) => 
        c.copy(algorithms = v.split(",")) 
      } text("comma-separated list of algorithms to be used for compressing the proof - sequential composition of algorithms is denoted by \"(Alg1*Alg2*...*Alg_n)\"")
      
      opt[String]('o', "outputformat") action { (v, c) => 
        c.copy(outputformat = v) 
      } text("proof format to be used for the compressed proofs")
      
      opt[Unit]("csv") action { (_, c) =>
        c.copy(csv = true) 
      } text("activates output of proof compression statistics to a csv file")
      
      opt[String]('b', "batch") action { (v, c) => 
        c.copy(inputs = c.inputs ++ fromFile(v).getLines) 
      } text("file containing one proof filename per line")
      
      arg[String]("<file>...") unbounded() optional() action { (v, c) =>
        c.copy(inputs = c.inputs ++ Seq(v)) 
      } text("filenames of the proof files")
    }
    // parser.parse returns Option[C]
    parser.parse(args, Config()) map { config =>
      
      println()
        
      // measurement table initialized with its header only
      // rows with data for every input or output proof are added during execution 
      // and the table is displayed to the user at the end
      var measurementTable: Seq[Seq[Any]] = Seq(Seq("Proof", "Length", "Core", "Height")) 
      
      val csvFile = new File(config.algorithms.mkString(",") + ".csv")
      
      // convenient method for writing compression statistics in a csv file
      val csvWriter = if (config.csv) Some(new FileWriter(csvFile,true))
                      else None
      def writeToCSV(s: String) = for (w <- csvWriter) w.write(s,0,s.length)
      
      val algcount = config.algorithms.size
      var lengths = Array.fill[Int](algcount+1)(0)
     
      if (config.csv) {
        var reader:BufferedReader = null
        try{
          reader = new BufferedReader(new FileReader(csvFile))
          var currLine = reader.readLine()
          var lastLine = ""
          
          while (currLine != null) {
            lastLine = currLine
            currLine = reader.readLine()
          }
          if (!(lastLine.equals(""))) {
            val split = lastLine.split(",")
            lengths(0) = split(4).toInt
            for (i <- 1 to algcount)
              lengths(i) = split(3+i*5).toInt
          }
        } finally try { reader.close }
      }
      

      
      
      val writeHeader = (config.csv && csvFile.length == 0)
      
      if (writeHeader) writeCSVHeader
      
      def writeCSVHeader = {
        writeToCSV("\t,Original,\t,\t,\t,")
        config.algorithms.foreach(a => writeToCSV(a+",\t,\t,\t,\t,"))
        writeToCSV("\n\t,")
        writeToCSV("\tLength,\tWidth,\tHeight,\tTotal length,")
        for (i <- 1 to (config.algorithms.size)) writeToCSV("\tLength,\tWidth,\tHeight,\tTotal length,\tCompression Ratio,")
        writeToCSV("\n")
      }
      
      
      
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
        
        lengths(0) = lengths(0)+mIProof.toSeq(0)
        writeToCSV(lengths(0)+",")
        
        
        val writeProof =  {
          config.outputformat match {
            case "smt2" => (p: Proof[N], name: String) => ProofExporterVeriT.write(p, name)
            case "skeptik" => (p: Proof[N], name: String) => ProofExporterSkeptik.write(p, name)
            case "" =>  (p: Proof[N], name: String) => { }
          }
        }
        
        var alg = 1
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
          lengths(alg) = lengths(alg)+mOProof.toSeq(0)
          writeToCSV(lengths(alg)+",")
          
          writeToCSV((100 - Math.round(1000.0*lengths(alg)/lengths(0))/10.0)+"%,")
          
          // Adding measurements to measurement table
          val outputRow = {
            val compressions = (mIProof.toSeq zip mOProof.toSeq) map { case (i,o) => 
              (Math.round(1000.0*o/i)/10.0) + "%"
            }  
            Seq(oProofName) ++ ((mOProof.toSeq zip compressions) map {case (o,c) => o + " (" + c + ")"}) 
          }
          measurementTable ++= Seq(outputRow)
          alg = alg + 1
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
    Core = number of axioms in the proof
    Height = length of longest path from leaf to root
          
""")
                    
    } getOrElse { // arguments are bad 
      print(
"""
Available algorithms are the following, as well as their sequential compositions:
""" + (for (a <- at.logic.skeptik.algorithm.compressor.algorithms) yield a._1).mkString(",  ") + "\n" +
"""
Available proof formats are:
  smt2    - VeriT's proof format
  skeptik - Skeptik's proof format

Example:
  The following command processes the proof 'eq_diamond9.smt2' using the
  algorithms 'RP' and the sequential composition of 'DAGify', 'RPI' and 'LU'.
  The compressed proofs are written using 'skeptik' proof format.
  And a csv file containing compression statistics is produced.
  
  compress -csv -a RP,(DAGify*RPI*LU) -o skeptik examples/proofs/VeriT/eq_diamond9.smt2
  
"""
      )      
    } 
  }
}
