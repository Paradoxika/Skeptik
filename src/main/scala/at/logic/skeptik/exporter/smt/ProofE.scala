package at.logic.skeptik.exporter
package smt

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}


trait ProofE extends SequentE {
  def write(proof:Proof[N]): Unit = {
    var counter = 0
    
    proof foldDown { 
      // premiseResults contains the chains used to derive the premise nodes.
      // for a node that has been named (e.g. axioms, unchecked inferences, and resolution nodes with more than one child), 
      // the corresponding chain contains only the created name.
      (n, premiseResults: Seq[String]) => {
        
        def beginInference(infName: String): String = {
          val name = ".c" + counter
          counter += 1
          write("(set " + name + " (" + infName)
          return name
        }
        
        def endInference() = {
          write(" :conclusion ")
          write(n.conclusion) 
          write("))\n")
          flush()
        }    
        n match {
          case Axiom(conclusion) => {
            val chain = beginInference("input")
            endInference()
            chain // only the name of the axiom
          }
          case R(left,right,_,_) => {
            val chain = premiseResults(0) + " " + premiseResults(1)
            if (proof.childrenOf(n).length == 1) {  // Note: this guarantees tree-like chains, but does not guarantee left-associativity of resolution chains
              chain
            }
            else {
              val chain = beginInference("resolution")
              write(" :clauses (" + chain + ")") 
              endInference()
              chain // only the name of the resolution node
            }
          }
          case UncheckedInference(infName, premises, conclusion) => {
            val chain = beginInference(infName)
            if (!premiseResults.isEmpty) write(" :clauses " + premiseResults.mkString("("," ",")"))
            endInference()
            chain // only the name of the unchecked inference
          }
        }  
      } 
    }
  }
}
