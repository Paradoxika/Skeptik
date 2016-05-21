package at.logic.skeptik.exporter
package smt

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import at.logic.skeptik.proof.sequent.lk.{TheoryR, TheoryLemma, EqReflexive, EqTransitive, EqCongruent, EqSymmetric}

trait ProofE extends SequentE {
  def omitConclusion: Boolean
  def avoidChains: Boolean
  
  def write(proof:Proof[N]): Unit = {
    var counter = 1
    
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
        
        def endInference(withConclusion: Boolean = true) = {
          if (withConclusion) {
            write(" :conclusion ")
            write(n.conclusion)  
          }
          write("))\n")
          flush()
        }  
        
        def chain(infName: String) = {
            val chain = premiseResults(0) + " " + premiseResults(1)
            if (!avoidChains && proof.childrenOf(n).length == 1) {  // Note: this guarantees tree-like chains, but does not guarantee left-associativity
              chain
            }
            else {
              val name = beginInference(infName)
              write(" :clauses (" + chain + ")") 
              endInference(!omitConclusion)
              name // chain containing only the name of the resolution node
            }
          }
        
        n match {
          case Axiom(_) => {
            val name = beginInference("input")
            endInference()
            name // chain containing only the name of the axiom
          }
          case TheoryR(left,right,_,_) => chain("th_resolution") 
          case R(left,right,_,_) => chain("resolution")
          case TheoryLemma(_) => {
            val name = beginInference("th_lemma")
            endInference()
            name
          }
          case EqReflexive(_) => {
            val name = beginInference("eq_reflexive")
            endInference()
            name
          }
          case EqTransitive(_) => {
            val name = beginInference("eq_transitive")
            endInference()
            name
          }
          case EqCongruent(_) => {
            val name = beginInference("eq_congruent")
            endInference()
            name
          }
          case EqSymmetric(_) => {
            val name = beginInference("eq_symmetric")
            endInference()
            name
          }
          case UncheckedInference(infName, premises, conclusion) => {
            val name = beginInference(infName)
            if (!premiseResults.isEmpty) write(" :clauses " + premiseResults.mkString("("," ",")"))
            endInference()
            name // chain containing only the name of the unchecked inference
          }
        }  
      } 
    }
  }
}
