package at.logic.skeptik.exporter
package skeptik

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import collection.mutable.{HashMap => MMap}

trait ProofE extends Exporter { 
  def deletionInfo: Boolean
  private val childrenVisited = MMap[N,Int]()
  private def deletionInfo(p: Proof[N], n: N, premiseResults: Seq[String]):String = {
    if (deletionInfo) {  
      val it = premiseResults.iterator
      var out = ""
      n.premises.foreach(pr => {
        val currString = it.next //should always have next, since the number of premises of n should coincide with the size of premiseResults
        val chV = childrenVisited.getOrElse(pr, 0) + 1
        childrenVisited.update(pr, chV)
        if (chV == p.childrenOf(pr).size) {
          if (!((p.childrenOf(pr).size == 1) && (pr.isInstanceOf[R]))) out += "(delete " + currString + ")\n"
        }
      })
      out
    }
    else ""
  }
  
  def write(proof:Proof[N]): Unit = {
    var counter = 0
    
    // ToDo: this could be cleaned up, as the SMT exporter. 
    // Possibly, code could be shared between them.
    proof foldDown { 
      (n, premiseResults: Seq[String]) => {
         
        println("hi") 
         
        n match {
          case Axiom(clause) => {
              val name = counter.toString
              counter += 1
              val line = name + " = " + "axiom(){ " + clause + " }\n"
              write(line, 0, line.length())
              name
          }
          case R(left,right,pivot,_) => {
            if (proof.childrenOf(n).length == 1) {
              "(" + premiseResults.head + " [" + pivot + "] " + premiseResults.last + ")"
            }
            else {
              val name = counter.toString
              counter += 1
              val subproof = "(" + premiseResults.head + " [" + pivot + "] " + premiseResults.last + ")"
              val line = name + " = " + subproof + "{ " + n.conclusion + " }\n" + deletionInfo(proof,n,premiseResults)
              write(line)
              name
            }
          }
          case UncheckedInference(infName, premises, conclusion) => {
            val name = counter.toString
            counter += 1
            val line = name + " = " + infName + "(" + premiseResults.mkString(" ") + "){ " + conclusion + " }\n" + deletionInfo(proof,n,premiseResults)
            write(line)
            name
          }
        }  
      } 
    }
  }
}

