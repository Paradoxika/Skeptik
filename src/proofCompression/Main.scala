/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression


import scala.collection.mutable._
import proofCompression.Utilities._
import proofCompression.ResolutionCalculus._
import proofCompression.Hypergraph._
import proofCompression.GUI._
import proofs._

object Main {
  /**
   * @param args the command line arguments
   */
  def main(args: Array[String]): Unit = {

//    val gui = new HypergraphVisualizer
//
//
////    for (i <- 1 to 10) {
    val g4 = new ResolutionHypergraph(PigeonProof.clempty)

    println("INITIAL GRAPH:")
    println(g4)

    g4.simplify

    println("FINAL RESULT:")
    println(g4)

    println(proofLength(PigeonProof.clempty))
////    }
////
////
//
    val g3 = new ResolutionHypergraph(Proof2.clempty)

//    gui.displayHypergraph(g3)

    println("INITIAL GRAPH:")
    println(g3)

    g3.simplify

    println("FINAL RESULT:")
    println(g3)

    println(proofLength(Proof2.clempty))
  

//    val g2 = new ResolutionHypergraph(P4.cl1115)
//    val g2 = new ResolutionHypergraph(P4.cl1116)
//    val g2 = new ResolutionHypergraph(P4.cl1138) Solved
//    val g2 = new ResolutionHypergraph(P4.cl1139) Solved
//    val g2 = new ResolutionHypergraph(P4.cl1140) Solved

//    val g2 = new ResolutionHypergraph(P4.cl1141) // Hard

//    val g2 = new ResolutionHypergraph(P4.cl1142) Solved
//    val g2 = new ResolutionHypergraph(P4.cl1143) Solved

//    val g2 = new ResolutionHypergraph(P4.cl1144) Solved
    //
//    val g2 = new ResolutionHypergraph(P4.cl1145) Solved from 1145 to 1148

//    val g2 = new ResolutionHypergraph(P4.cl1149) Solved until 1154

//    val f = P4.cl1155

    //val f = P4.cl1180
//    val g2 = new ResolutionHypergraph(f)

//    val g2 = new ResolutionHypergraph(P4.cl1200)
//    val g2 = new ResolutionHypergraph(P4.cl1200)
//    val g2 = new ResolutionHypergraph(P4.cl1200)
//    val g2 = new ResolutionHypergraph(P4.cl1170)
//    val g2 = new ResolutionHypergraph(P4.cl1200)
//    val g2 = new ResolutionHypergraph(P4.clempty)


    val f = Proof0.c8
    val g = new ResolutionHypergraph(f)

    val gui = new HypergraphVisualizer
    gui.displayHypergraph(g)

    println("INITIAL GRAPH:")
    println(g)
////
    g.simplify
////
    println("FINAL RESULT:")
    println(g)
////
    println(proofLength(f))

    
  }
}
