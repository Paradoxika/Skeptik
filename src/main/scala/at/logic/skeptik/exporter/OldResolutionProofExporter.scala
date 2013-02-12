package at.logic.skeptik

import scala.util.parsing.combinator._
import at.logic.skeptik.proof.oldResolution._
import collection.mutable._
import java.io.FileWriter

package object exporter {
  def writeProofNodeToFile(proof:ProofNode, filename: String)(implicit maxUnnamedResolvents: Int) = {
    var unnamedResolventsCounter = 0
    var counter = 0
    val visitedProofNodes = new HashMap[ProofNode,String]
    val writer = new FileWriter(filename)
    def writeProofNodeToFileRec(p:ProofNode): String = {
      if (visitedProofNodes.contains(p)) return visitedProofNodes(p)
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
              visitedProofNodes += (p -> name)
              return name
            }
          }
          case Resolvent(left,right) => {
            val leftString = writeProofNodeToFileRec(left)
            val rightString = writeProofNodeToFileRec(right)
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
              visitedProofNodes += (p -> name)
              return name
            }
          }
        }
      }
    }
    writeProofNodeToFileRec(proof)
    val lastLine = "qed = " + (counter-1)
    writer.write(lastLine, 0, lastLine.length)
    writer.close
  }
}
