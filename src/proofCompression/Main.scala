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
import proofCompression.ProofRegularization._
import proofCompression.ProofDAGification._
import proofs._
import proofCompression._
import evaluation._

object Main {
  /**
   * @param args the command line arguments
   */
  def main(args: Array[String]): Unit = {

//    val gui = new HypergraphVisualizer
//    gui.displayHypergraph(g3)
//

//    val writer = new FileWriter("myfile2.test")
//    writer.write("hello world", 7, 1)
//    writer.close

    val directory = "proofs/BWPProofs/"
    val proofFiles = List("TheFirstChallenge2",
                          "TheFirstChallenge1",
                          "TheFirstChallenge",
                          "pigeon(3)(2)",
                          "DAGifiableTree",
                          "SMT2010",
                          "irregularWithProblematicLiterals",
                          "irregularWithoutProblematicLiterals",
                          "simple")

    Experimenter.run(directory, proofFiles, "output201011241636.txt")
    println("yes")
    Experimenter.runHypergraph(directory, proofFiles, "output.txt")
   


      //for (p <- List("proofs/BWPProofs/DAGifiableTree.proof").map(file => ProofParser.getProofFromFile(file))) {
      //for (p <- List("proofs/BWPProofs/pigeon(3)(2).proof").map(file => ProofParser.getProofFromFile(file))) {
      //for (p <- List("proofs/PascalProofs/TheFirstChallenge.proof").map(file => ProofParser.getProofFromFile(file))) {
//      for (p <- List("proofs/PascalProofs/TheFirstChallenge2.proof", "proofs/BWPProofs/pigeon(3)(2).proof").map(file => ProofParser.getProofFromFile(file))) {
//
//
//
//        println(p)
//        println("Proof Length:" + proofLength(p))
//        println("Is regular? : " + isRegular(p))
//        println("Is DAG? : " + isNonTree(p))
//        regularize(p)
//        println("Regularized Proof Length:" + proofLength(p))
//        fixProof(p)
//        println("Fixed Proof Length:" + proofLength(p))
//        println("Is regular? : " + isRegular(p))
//        DAGify(p)
//        println("DAGified Proof Length:" + proofLength(p))
//        println("Final Clause :" + p.clause)
//        println()
//      }

//    val g4 = new ResolutionHypergraph(PigeonProof.clempty)
//
//    println("INITIAL GRAPH:")
//    println(g4)
//
//    g4.simplify
//
//    println("FINAL RESULT:")
//    println(g4)
//
//    println(proofLength(PigeonProof.clempty))
//
//
//
//    val g3 = new ResolutionHypergraph(Proof2.clempty)
//
//
//
//    println("INITIAL GRAPH:")
//    println(g3)
//
//    g3.simplify
//
//    println("FINAL RESULT:")
//    println(g3)
//
//    println(proofLength(Proof2.clempty))
//

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


//    val f = Proof0.c8
//    val g = new ResolutionHypergraph(f)
//
//    val gui = new HypergraphVisualizer
//    gui.displayHypergraph(g)
//
//    println("INITIAL GRAPH:")
//    println(g)
//////
//    g.simplify
//////
//    println("FINAL RESULT:")
//    println(g)
//////
//    println(proofLength(f))

    
  }
}
