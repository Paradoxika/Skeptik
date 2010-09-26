/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

import scala.collection.mutable._
import resolutionproofcompression.Utilities._
import resolutionproofcompression.ResolutionCalculus._
import resolutionproofcompression.Hypergraph._

object Main {
  /**
   * @param args the command line arguments
   */
  def main(args: Array[String]): Unit = {
//    val g = new ResolutionHypergraph(PigeonProof.clempty)
//
//    println("INITIAL GRAPH:")
//    println(g)
//
//    g.simplify
//
//    println("FINAL RESULT:")
//    println(g)
//
//    println(proofLength(PigeonProof.clempty))

//    val g2 = new ResolutionHypergraph(P4.cl1115)
//    val g2 = new ResolutionHypergraph(P4.cl1116)
    val g2 = new ResolutionHypergraph(P4.cl1138)

    

    println("INITIAL GRAPH:")
    println(g2)

    g2.simplify

    println("FINAL RESULT:")
    println(g2)
    
    println(proofLength(P1.cl799))
  }
}
