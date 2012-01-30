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
  def writeProofToFile(proof:Proof, filename: String)(implicit maxUnnamedResolvents: Int) = {
    var unnamedResolventsCounter = 0
    var counter = 0
    val visitedProofs = new HashMap[Proof,String]
    val writer = new FileWriter(filename)
    def writeProofToFileRec(p:Proof): String = {
      if (visitedProofs.contains(p)) return visitedProofs(p)
      else {
        p match {
          case Input(_) => {
            if (p.children.length == 1) p.toString
            else {
              val name = counter.toString
              counter += 1
              val clause = p.toString
              val line = name + " = " + clause + "\n"
              writer.write(line, 0, line.length)
              visitedProofs += (p -> name)
              return name
            }
          }
          case Resolvent(left,right) => {
            val leftString = writeProofToFileRec(left)
            val rightString = writeProofToFileRec(right)
            if (p.children.length == 1 && unnamedResolventsCounter <= maxUnnamedResolvents) {
              unnamedResolventsCounter += 1
              "(" + leftString + "." + rightString + ")"
            }
            else {
              unnamedResolventsCounter = 0
              val name = counter.toString
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
    writeProofToFileRec(proof)
    val lastLine = "qed = " + (counter-1)
    writer.write(lastLine, 0, lastLine.length)
    writer.close
  }
}
