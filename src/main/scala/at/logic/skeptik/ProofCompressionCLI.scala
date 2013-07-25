package at.logic.skeptik

import at.logic.skeptik.parser.{ProofParser,ProofParserVeriT,ProofParserSkeptik,AlgorithmParser}
import at.logic.skeptik.exporter.{ProofExporterVeriT,ProofExporterSkeptik}
import at.logic.skeptik.judgment.Judgment
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.time._
import at.logic.skeptik.util.pretty._

import scalax.io.{Resource,Seekable}


object ProofCompressionCLI {

  case class Config(inputs: Seq[String] = Seq(),
                    directory: String = "",
                    algorithms: Seq[String] = Seq(), 
                    outputformat: String = "",
                    csv: Option[Seekable] = None,
                    cr: Option[Seekable] = None,
                    verbose: Boolean = true)                

    
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
      
      note(
      """
        <alg> can be any of the following atomic algorithms:
      """ + 
      (for (a <- at.logic.skeptik.algorithm.compressor.algorithms) yield a._1).mkString(",") + "\n" + 
      """
        or a sequential composition denoted by '(alg1*alg2*...*algN)'
      """    
      )  
      
      opt[String]("algorithms") action { (v, c) => 
        c.copy(algorithms = c.algorithms ++ Resource.fromFile(c.directory + v).lines()) 
      } text("use algorithms listed in <file>\n") valueName("<file>")
      
      opt[String]('d', "directory") unbounded() action { (v, c) => 
        c.copy(directory = v)
      } text("set working directory to <dir>") valueName("<dir>")
      
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
        c.copy(csv = Some(Resource.fromFile(c.directory + c.algorithms.mkString(",") + ".csv"))) 
      } text("output statistics to a csv file\n")
      
      opt[Unit]("cr") action { (_, c) =>
        c.copy(cr = Some(Resource.fromFile(c.directory + c.algorithms.mkString(",") + "-CR.csv"))) 
      } text("output compression ratios to a csv file")
      
      opt[Unit]("silent") action { (_, c) =>
        c.copy(verbose = false) 
      } text("switch off verbosity")
      
      opt[String]('p', "proofs") action { (v, c) => 
        c.copy(inputs = c.inputs ++ (Resource.fromFile(c.directory + v).lines() map {c.directory + _})) 
      } text("compress proofs from files listed in <file>\n") valueName("<file>")
      
      arg[String]("<proof-file>...") unbounded() optional() action { (v, c) =>
        c.copy(inputs = c.inputs ++ Seq(c.directory + v)) 
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
      
      
      def log(s: Any) = if (config.verbose) print(s)

      log("\n")
         
      if (config.inputs.isEmpty) parser.showUsage
      else {

        // measurement table initialized with its header only
        // rows with data for every input or output proof are added during execution 
        // and the table is displayed to the user at the end
        var measurementTable: Seq[Seq[Any]] = Seq(Seq("Proof", "Length", "Core", "Height")) 
        def appendAtMeasurementTable(row: Seq[Any]) = measurementTable ++= Seq(row)
        def showMeasurementTable() = {
          log("\n")
          log(prettyTable(measurementTable))
          log(""" 
            where:           
              Length = number of inferences in the proof
              Core = number of axioms in the proof
              Height = length of longest path from leaf to root         
          """ + "\n")
        }
        
        val algcount = config.algorithms.size
        // initialize last written parameter sums of algorithms and uncompressed proofs with 0
        var heights = Array.fill[Int](algcount+1)(0)
        var widths = Array.fill[Int](algcount+1)(0)
        var lengths = Array.fill[Int](algcount+1)(0)
       
        // read off last written total lengths
//        for (f <- config.cr if f.exists) { 
//          val lastline = fromFile(f).getLines.toSeq.last
//          val last = lastline.split(",")
//          lengths(0) = last(0).toInt
//          widths(0) = last(1).toInt
//          heights(0) = last(2).toInt
//          for (i <- 1 to algcount) {
//            lengths(i) = last(3+(i-1)*6).toInt
//            widths(i) = last(4+(i-1)*6).toInt
//            heights(i) = last(5+(i-1)*6).toInt
//          }
//        }
                
        def append(ow: Option[Seekable])(s: String) = ow map { _.append(s)}
        
//        // method for writing to the CR file
//        val crWriter = config.cr map { f => new FileWriter(f,true)}

        // writing header if file is empty 
//        for (f <- config.csv if f.length == 0) {
//          writeToCSV("\tProof,Uncompressed,\t,\t,")
//          config.algorithms.foreach(a => writeToCSV(a+",\t,\t,"))
//          writeToCSV("\n\t,")
//          writeToCSV("\tLength,\tWidth,\tHeight,")
//          for (i <- 1 to algcount) writeToCSV("\tLength,\tWidth,\tHeight,")
//          writeToCSV("\n")
//        }
        
        // CR file overwrites instead of appending, therefore header is always written if cr is set to true
        for (f <- config.cr) {
          append(config.cr)("\tUncompressed,\t,\t,")
          config.algorithms.foreach(a => append(config.cr)("\t"+a+",\t,\t,\t,\t,\t,"))
          append(config.cr)("\n")
          append(config.cr)("\tLength,\tWidth,\tHeight,")
          for (i <- 1 to algcount) append(config.cr)("\tLength,\tWidth,\tHeight,\tCR - length,\tCR - width,\tCR - height,")
          append(config.cr)("\n")
        }
        

        for (filename <- config.inputs) {
          // Reading the proof
          log("Reading and checking proof '"+ filename +"' ...")
          val proofFormat = ("""\.[^\.]+$""".r findFirstIn filename) getOrElse { throw new Exception(unknownFormat(filename)) }
          val proofName = filename.split(proofFormat)(0) // filename without extension
          val proofParser = proofFormat match {
            case ".smt2"  => ProofParserVeriT
            case ".skeptik"  => ProofParserSkeptik
          }
          val Timed(proof, tRead) = timed { proofParser.read(filename) }   
          log(completedIn(tRead) + "\n")
          
          // Measuring the input Proof
          log("Measuring '"+ proofName +"' ...")
          val Timed(mIProof,tMIProof) = timed { measure(proof) }
          log(completedIn(tMIProof) + "\n")
          
          // Adding measurements to measurement table
          val inputRow = (Seq(proofName) ++ mIProof.toSeq)
          appendAtMeasurementTable(inputRow)
          
          // Adding measurements to csv file
          append(config.csv)(proofName + mIProof.toSeq.mkString(",",",", ","))

          
          // compute and write new values to CR file
          lengths(0) += mIProof.toSeq(0)
          widths(0) += mIProof.toSeq(1)
          heights(0) += mIProof.toSeq(2)
          append(config.cr)(lengths(0) + "," + widths(0) + "," + heights(0) + ",")
          
          
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
            log("Compressing with algorithm: " + a + "...")
            val Timed(p, t) = timed { algorithm(proof) }
            log(completedIn(t) + "\n")
            
            val oProofName = proofName + "-" + a
            log("Writing compressed proof '" + oProofName + "'...")
            val Timed(_,w) = timed { writeProof(p, oProofName) }
            log(completedIn(w) + "\n")
            
            log("Measuring '"+ oProofName +"' ...")
            val Timed(mOProof,tMOProof) = timed { measure(p) }
            log(completedIn(tMOProof) + "\n")
            
            // Adding measurements to csv file
            append(config.csv)(mOProof.toSeq.mkString("",",", ","))

            // compute and write new values to CR file
            lengths(alg) += mOProof.toSeq(0)
            widths(alg) += mOProof.toSeq(1)
            heights(alg) += mOProof.toSeq(2)
          
            append(config.cr)(lengths(alg)+","+widths(alg)+ ","+heights(alg)+",")
            append(config.cr)((100 - Math.round(1000.0*lengths(alg)/lengths(0))/10.0)+"%,")
            append(config.cr)((100 - Math.round(1000.0*widths(alg)/widths(0))/10.0)+"%,")
            append(config.cr)((100 - Math.round(1000.0*heights(alg)/heights(0))/10.0)+"%,")
          
            
            // Adding measurements to measurement table
            val outputRow = {
              val compressions = (mIProof.toSeq zip mOProof.toSeq) map { case (i,o) => 
                (Math.round(1000.0*o/i)/10.0) + "%"
              }  
              Seq(oProofName) ++ ((mOProof.toSeq zip compressions) map {case (o,c) => o + " (" + c + ")"}) 
            }
            appendAtMeasurementTable(outputRow)

            alg = alg + 1
          } 
          append(config.csv)("\n")
          append(config.cr)("\n")
        } // end of 'for (filename <- config.inputs)'
        
        // Displaying proof measurements  
        showMeasurementTable()
      } // end of else of 'if (config.inputs.isEmpty)'
            
    } getOrElse { // arguments are bad 
     
    } 
  }
}
