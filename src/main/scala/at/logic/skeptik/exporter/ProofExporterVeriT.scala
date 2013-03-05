package at.logic.skeptik.exporter

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{CutIC, Axiom}
import java.io.FileWriter



object ProofExporterVeriT {
  def writeProofToFile(proof:Proof[Node], filename: String) = {
    val writer = new FileWriter(filename)
    
    var counter = 0
    
    proof foldDown { 
      (n, premiseResults: Seq[String]) => {
        n match {
          case Axiom(clause) => {
              val name = ".c" + counter
              counter += 1
              val line = "(set " + name + " (input :conclusion " + clause + "))\n"
              writer.write(line, 0, line.length)
              name
          }
          case CutIC(left,right,_,_) => {
            if (proof.childrenOf(n).length == 1) {
              "(" + premiseResults(0) + " " + premiseResults(1) + ")"
            }
            else {
              val name = ".c" + counter
              counter += 1
              val subproof = "(" + premiseResults(0) + " " + premiseResults(1) + ")"
              val line = "(set " + name + " (resolution :clauses " + subproof + "))\n"
              writer.write(line, 0, line.length)
              name
            }
          }
        }  
      } 
    }
 
    writer.close
  }
}
