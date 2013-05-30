package at.logic.skeptik.exporter

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import java.io.FileWriter

// ToDo: This is almost VeriT's proof format. 
// Conclusion from resolutions is omitted.
// Clauses (Sequents) are just output with their toString method.
// Premises are not given as a left-associative list, but as parenthesized tree. 
// It is not worth making it perfect now, 
// because VeriT's format will most likely change significantly in the future.

object ProofExporterVeriT extends ProofExporter[Node] {
  def write(proof:Proof[Node], filename: String) = {
    val writer = new FileWriter(filename + ".smt2")
    def write(s: String) = writer.write(s, 0, s.length)
    
    var counter = 0
    
    proof foldDown { 
      (n, premiseResults: Seq[String]) => {
        n match {
          case Axiom(clause) => {
              val name = ".c" + counter
              counter += 1
              write("(set " + name + " (input :conclusion " + clause + "))\n")
              name
          }
          case R(left,right,_,_) => {
            if (proof.childrenOf(n).length == 1) {
              "(" + premiseResults(0) + " " + premiseResults(1) + ")"
            }
            else {
              val name = ".c" + counter
              counter += 1
              val subproof = "(" + premiseResults(0) + " " + premiseResults(1) + ")"
              write("(set " + name + " (resolution :clauses " + subproof + "))\n")
              name
            }
          }
          case UncheckedInference(infName, premises, conclusion) => {
            val name = ".c" + counter
            counter += 1
            write("(set " + name + " (" + infName + " :clauses " + premiseResults.mkString(" ") + " :conclusion " + conclusion + "))\n")
            name
          }
        }  
      } 
    }
 
    writer.close()
  }
}
