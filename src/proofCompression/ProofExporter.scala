/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import scala.util.parsing.combinator._
import proofCompression.ResolutionCalculus._
import scala.collection.mutable._
import java.io.FileWriter

object ProofExporter {
  def writeProofToFile(proof:ResolutionProof, filename: String) = {
    var counter = 0
    val writer = new FileWriter(filename)
    def writeProofToFileRec(p:ResolutionProof, visitedProofs: HashMap[ResolutionProof,String]): String = {
      if (visitedProofs.contains(p)) return visitedProofs(p)
      else {
        p match {
          case Input(_) => {
            if (p.children.length == 1) p.toString
            else {
              val name = "c" + counter
              counter += 1
              val clause = p.toString
              val line = name + " = " + clause + "\n"
              writer.write(line, 0, line.length)
              visitedProofs += (p -> name)
              return name
            }
          }
          case Resolvent(left,right) => {
            val leftString = writeProofToFileRec(left, visitedProofs)
            val rightString = writeProofToFileRec(right, visitedProofs)
            if (p.children.length == 1) "(" + leftString + "." + rightString + ")"
            else {
              val name = "c" + counter
              counter += 1
              val subproof = "(" + leftString + "." + rightString + ")"
              val line = name + " = " + subproof + "\n"
              writer.write(line, 0, line.length)
              visitedProofs += (p -> name)
              return name
            }
          }
        }
      }
    }
    writeProofToFileRec(proof, new HashMap[ResolutionProof,String])
    val lastLine = "qed = c" + (counter-1)
    writer.write(lastLine, 0, lastLine.length)
    writer.close
  }

}
