package at.logic.skeptik.exporter
package skeptik

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference}
import java.io.FileWriter
import scala.collection.mutable.{HashMap => MMap}

trait outDeleteInfo {
  def getDeleteInfo(p: Proof[Node], n: Node, premiseResults: Seq[String]):String = ""
  def extension: String = "skeptik"
}

trait deleteInfo {
  def extension: String = "skeptikD"
  
  val childrenVisited = MMap[Node,Int]()
  def getDeleteInfo(p: Proof[Node], n: Node, premiseResults: Seq[String]):String = {
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
}

object ProofExporterSkeptik extends AbstractProofExporterSkeptik with outDeleteInfo

object ProofExporterSkeptikD extends AbstractProofExporterSkeptik with deleteInfo

abstract class AbstractProofExporterSkeptik {
  
  def getDeleteInfo(p: Proof[Node], n: Node, premiseResults: Seq[String]):String
  
  def extension: String
  
  def write(proof:Proof[Node], filename: String) = {
    val writer = new FileWriter(filename + "." + extension)
    
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
          case R(left,right,pivot,_) => {
            if (proof.childrenOf(n).length == 1) {
              "(" + premiseResults.head + " [" + pivot + "] " + premiseResults.last + ")"
            }
            else {
              val name = counter.toString
              counter += 1
              val subproof = "(" + premiseResults.head + " [" + pivot + "] " + premiseResults.last + ")"
              val line = name + " = " + subproof + "{ " + n.conclusion + " }\n"+ getDeleteInfo(proof,n,premiseResults)
              writer.write(line, 0, line.length)
              name
            }
          }
          case UncheckedInference(infName, premises, conclusion) => {
            val name = counter.toString
            counter += 1
            val line = name + " = " + infName + "(" + premiseResults.mkString(" ") + "){ " + conclusion + " }\n" + getDeleteInfo(proof,n,premiseResults)
            writer.write(line, 0, line.length)
            name
          }
        }  
      } 
    }
    writer.close()
  }
}
