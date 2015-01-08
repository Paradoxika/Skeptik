package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.{Proof}

import java.io.{File, FileReader, FileWriter, BufferedReader}

import language.postfixOps 
import sys.process._

object ProofParserTraceCheckTrim extends ProofParser[N] {
  def read(filename: String) : Proof[N] = {
    val filenameSplit = filename.split('.')
    val name = filenameSplit.dropRight(1).mkString(".") // remove extension from filename
        
    println("converting '.tct' file to pre '.cnf' file")
    // sort trace2.tct -n | grep " 0 0" | sed 's| 0 0| 0|' | cut -d' ' -f2-
    Process("sort " + filename + " -n") #> 
      Process(Seq("grep", " 0 0")) #>
        Process(Seq("sed", "s| 0 0| 0|")) #> 
          Process(Seq("cut", "-d", " ", "-f2-")) #>> new File(name + ".aux.cnf") !
 
    // println("getting number of clauses in pre '.cnf' file")
    // grep -w "0" -c trace2.temporary.cnf
    val numClauses = (Seq("grep", "-w", "0", "-c", name + ".aux.cnf") !!).split("\n").head.toInt
    
    // println("getting number of vars in pre '.cnf' file ")
    // xargs -n1 < trace2.temporary.cnf | sed 's|-||' | sort -n -r | head -n1
    val numVars = (new File(name + ".aux.cnf") #> Seq("xargs", "-n1") #> Seq("sed", "s|-||") #> Seq("sort", "-n", "-r") #> "head -n1" !!).split("\n").head.toInt
        
    val header = "p cnf " + numVars + " " + numClauses
    
    val fw = new FileWriter(name + ".temporary.cnf", true) 
    val fr = new FileReader(name + ".aux.cnf")
    val br = new BufferedReader(fr)
    try { 
      fw.append(header + System.lineSeparator())
      var l = br.readLine()
      while (l != null) { fw.append(l + System.lineSeparator()); l = br.readLine(); } 
    } finally { fw.close(); br.close(); fr.close() ;}
    
    
    println("converting '.tct' file to '.drup' file")
    // sort trace -n | grep -v " 0 0" | sed 's| 0 [1-9][ 0-9]* 0| 0|' | cut -d' ' -f2-
    Process("sort " + filename + " -n") #> 
      Process(Seq("grep", "-v", " 0 0")) #>
        Process(Seq("sed", "s| 0 [1-9][ 0-9]* 0| 0|")) #> 
          Process(Seq("cut", "-d", " ", "-f2-")) #>> new File(name + ".temporary.drup") !
    
    println("reading DRUP proof")
    val p = ProofParserDRUP.read(name + ".temporary.drup")
    
    println("deleting temporary files")
    "rm " + name + ".temporary.drup" ! ;
    "rm " + name + ".temporary.cnf" ! ;
    "rm " + name + ".aux.cnf" ! ;
    
    p
  }
}