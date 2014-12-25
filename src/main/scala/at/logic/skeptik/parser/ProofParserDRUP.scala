package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.{Proof}

import java.io.FileReader
import java.io.File

import language.postfixOps 
import sys.process._

object ProofParserDRUP extends ProofParser[N] {
  def read(filename: String) : Proof[N] = {
    val filenameSplit = filename.split('.')
    val extension = filenameSplit.last
    val name = (filenameSplit.dropRight(1) :\ "")(_ + _)
    
    // println("obtaining lemmas")
    "./lib/drat-trim/drat-trim " + 
    name + ".cnf " + filename + " -l " + name + ".lemmas.drup" !
    
    // println("converting to tracecheck")
    "./lib/drat-trim/drat-trim " + 
    name + ".cnf " + name + ".lemmas.drup -f -r " + name + ".temp.tc" !
    
    // println("sorting tracechek")
    Process("sort " + name + ".temp.tc -n") #>> new File(name + ".tc") !
    
    // println("deleting temporary files")
    "rm " + name + ".lemmas.drup" ! ;
    "rm " + name + ".temp.tc" ! ;
    
    // println("reading tracecheck")
    ProofParserTraceCheck.read(name + ".tc")
  }
}