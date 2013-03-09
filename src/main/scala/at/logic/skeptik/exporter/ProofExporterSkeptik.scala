package at.logic.skeptik.exporter

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{CutIC, Axiom, UncheckedInference}
import java.io.FileWriter

object ProofExporterSkeptik extends ProofExporter[Node] {
  def write(proof:Proof[Node], filename: String) = {
    val writer = new FileWriter(filename)
    
    var counter = 0
    
    proof foldDown { 
      (n, premiseResults: Seq[String]) => {
        n match {
          case Axiom(clause) => {
              val name = counter.toString
              counter += 1
              val line = name + " = " + "axiom(){ " + clause + " }\n"
              writer.write(line, 0, line.length)
              name
          }
          case CutIC(left,right,pivot,_) => {
            if (proof.childrenOf(n).length == 1) {
              "(" + premiseResults.head + " [" + pivot + "] " + premiseResults.last + ")"
            }
            else {
              val name = counter.toString
              counter += 1
              val subproof = "(" + premiseResults.head + " [" + pivot + "] " + premiseResults.last + ")"
              val line = name + " = " + subproof + "{ " + n.conclusion + " }\n"
              writer.write(line, 0, line.length)
              name
            }
          }
          case UncheckedInference(infName, premises, conclusion) => {
            val name = counter.toString
            counter += 1
            val line = name + " = " + infName + "(" + premiseResults.mkString(" ") + "){ " + conclusion + " }\n"
            writer.write(line, 0, line.length)
            name
          }
        }  
      } 
    }
 
    writer.close
  }
}
