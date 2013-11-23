package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.io.{Input,Output,NoOutput,StandardOutput,FileOutput}
import scala.sys.process._

object SATPebbler {

//   var clauses = 0
  
  def correctPebbling(proof: Proof[N], file: Output) = {
    val n = proof.size
    for (m <- 1 to n) {
      file.write(m + " ")
    }    
    file.write("0\n")
//    clauses = clauses + 1
    for (i <- 1 to n) {
      val node = proof.nodes(n - i)
      val premises = node.premises
//      if (node.premises.isEmpty) println((n-i + 1) + " ~ " + node)
      val premiseNumbers = premises.map(pr => n - proof.nodes.indexOf(pr))
//      println(i +  " has Premises: " + premiseNumbers.mkString(","))
      
      for (l <- (1 to n) diff Seq(i)) { //Only 1 pebble in the beginning
        file.write(-i + " " + -l + " 0\n")
//        clauses = clauses + 1
      }
      if (!premises.isEmpty) {
        file.write(-i + " 0\n")
//        clauses = clauses + 1
      }
      for (j <- 0 to (n-2)) {
        //Node i was pebbled at time j+1
        val notIPebbled = (i + n*j) + " " + -(i + n*(j+1))
        
//        out = out + "c only one pebble\n"
        //Only 1 Pebble per turn
        for (h <- (1 to n) diff Seq(i)) {
          file.write(notIPebbled + " " + (h + n*j) + " " + -(h + n*(j+1)) + " 0\n")
//          out = out + notIPebbled + " " + -(h + n*j) + " " + (h + n*(j+1)) + " 0\n"
//          clauses = clauses + 1
        }
//        out = out + "c ------\n"
        
        //Correct pebbling
//        clauses = clauses + premiseNumbers.size
        file.write("c premises have to be pebbled\n")
        premiseNumbers.foreach(prN => file.write(notIPebbled + " " + (prN + j*n) + " 0\n"))
//        if (premiseNumbers.isEmpty) {
////          println(i + " has no Premises " + node.premises.isEmpty)
//          out = out + notIPebbled + " 0\n"
//          clauses = clauses + 1
//        }
        file.write("c ------\n")
      }
    }
    file.write((n*n) + " 0\n")
//    clauses = clauses + 1
//    out
  }
  
  def karySubset(proof: Proof[N], k: Int, file: Output): Unit = {
    val n = proof.size
    for (i <- 0 to (n-1)) {
      val low = 1 + i*n
      val high = (i+1)*n
      val subsets = -high to -low combinations k+1
      file.write(subsets.map(_.mkString(" ")).mkString(" 0\n") + " 0\n")
//      subsets.foreach(s => {
//        clauses = clauses + 1
//        out = out + s.mkString(" ") + " 0\n"
//      })
    }
  }
  
  def interpretSAT(filename: String, proof: Proof[N]) = {
    val n = proof.size
    val in = Input(filename)
    val lines = in.lines
    if (lines.size > 1) {
      val assign = lines.last.split(" ").map(_.toInt)
      for (i <- 0 to (n-1)) {
        for (j <- 0 to (n-1)) {
          if (i == 0) {
            if (assign(j + i*n) > 0) {
              println("init " + (j + 1))
            }
          }
          else {
            if ((assign(j + (i-1)*n) < 0) && (assign(j + i*n) > 0)) { 
              println("pebble " + (j + 1))
            }
            else if ((assign(j + (i-1)*n) > 0) && (assign(j + i*n) < 0)) {
              println("unpebble " + (j + 1))
            }
          }
        }
        println("-----")
      }
    }
  }
  
  def main(args: Array[String]): Unit = {
    val proof = ProofParserVeriT.read("examples/proofs/VeriT/eq_diamond2.smt2")
      val out = new FileOutput("experiments/SATPebble")
    out.clear
    println(proof)
//    proof.nodes.foreach(println)
    out.write("p cnf " + (proof.size*proof.size) + " 0\n")
    karySubset(proof, 4, out)
//    println(subs)
    correctPebbling(proof, out)
//    println(corr)
//    out.write("p cnf " + (proof.size*proof.size) + " " + clauses + "\n" + corr + subs)
    Executer.executeMini("experiments/msat", "experiments/SATPebble")
    interpretSAT("experiments/msat", proof)
  }
}


object Executer {

  def executeMini(fileName: String, parameters: String): Stream[String] = {
    val call = "minisat " + parameters + " " + fileName
    call.!
    val contents = Process(call).lines
    contents
  }
}
