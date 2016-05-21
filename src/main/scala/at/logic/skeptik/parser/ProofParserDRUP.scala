package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.{Proof}

import java.io.FileReader
import java.io.File

import language.postfixOps 
import sys.process._


/**
 * A DRUP proof is simply a list of clauses that have been learned 
 * by a SAT-solver during proof search, in chronological order. 
 * 
 * This parser makes an external call to Marijn Heule's DRAT-Trim tool
 * to convert the DRUP proof to an ordered trace, and then parses the 
 * ordered trace using ProofParserTraceCheckOrdered.
 * 
 * 
 * Issues:
 * 
 * 1) Currently, a pre-compiled DRAT-Trim executable is used. 
 *    As it was compiled for Mac OSX Yosemite, it is unlikely to
 *    work in other operating systems. In other operating systems,
 *    DRAT-Trim's source, available in the "\lib\drat-trim" folder
 *    must be manually compiled.
 *   
 */


object ProofParserDRUP extends ProofParser[N] {
  def read(filename: String) : Proof[N] = {
    val filenameSplit = filename.split('.')
    val extension = filenameSplit.last
    val name = filenameSplit.dropRight(1).mkString(".")
    
    println("obtaining lemmas")
    "./lib/drat-trim/drat-trim " + 
    name + ".cnf " + filename + " -l " + name + ".lemmas.drup" !
    
    println("converting to tracecheck")
    "./lib/drat-trim/drat-trim " + 
    name + ".cnf " + name + ".lemmas.drup -f -r " + name + ".temp.tc" !
    
    println("sorting tracecheck")
    Process("sort " + name + ".temp.tc -n") #>> new File(name + ".tco") !
    
    println("deleting temporary files")
    //"rm " + name + ".lemmas.drup" ! ;
    //"rm " + name + ".temp.tc" ! ;
    
    println("reading tracecheck file")
    println(name)
    ProofParserTraceCheckOrdered.read(name + ".tco")
  }
}