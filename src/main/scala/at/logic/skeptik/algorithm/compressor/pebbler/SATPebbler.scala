package at.logic.skeptik.algorithm.compressor.pebbler

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.proof.measure
import at.logic.skeptik.util.io.{Input,Output,NoOutput,StandardOutput,FileOutput}
import scala.sys.process._

/**
 * Translate problem of pebbling proof with k pebbles into SAT instance, 
 * as described in Space and Congruence Compression of Proofs
 */

object SATPebbler {

  def dimacs(k: Int, proof: Proof[N], out: FileOutput) = {
    
    val n = proof.size
    
    val axioms = proof.nodes.filter(node => node.premises.isEmpty).map(n - proof.nodes.indexOf(_))
    
    var clauses = 0
    
    def p(pebble: Int, node: Int, time: Int) = pebble + (node-1) * k + (time-1) * k * n
    
    def bigNodeDisjunction(pebble: Int, nodes: Range, time: Int) = {
      (p(pebble, nodes.min, time) to p(pebble, nodes.max, time) by n).mkString(" ") + " 0\n"
    }
    
    def notP1orNotP2(pebble1: Int, node1: Int, time1: Int, pebble2: Int, node2: Int, time2: Int) = {
      -p(pebble1,node1,time1) + " " + -p(pebble2, node2, time2) + " "
    }

    def pebbleRoot = {
//      clauses = clauses + 1
      (p(1,n,n) to p(k,n,n)).mkString(" ") + " 0\n"
    }
    
    def oneNodePerPebble = {
      (1 to k).map(x => {
        (1 to n).map(j => {
          (1 to n).map(t => {
            (1 to (j-1)).map(i => {
//              clauses = clauses + 1
              notP1orNotP2(x,j,t,x,i,t) + " 0\n"
            }).mkString("")
          }).mkString("")
        }).mkString("")
      }).mkString("")
    }
    
    def atLeast1Init = {
//      clauses = clauses + 1
      (1 to k).map(x => {
        axioms.map(j => {
          p(x,j,1) + " "
        }).mkString("")
      }).mkString("") + "0\n"
    }
    
    def onlyAxiomsInit = {
      (1 to k).map(x => {
        ((1 to n) diff axioms).map(j => {
//          clauses = clauses + 1
          -p(x,j,1) + " 0\n"
        }).mkString("")
      }).mkString("")
    }
    
    def atMost1Init = {
      (p(1,1,1) to p(k,n,1)).map(i => {
        (1 to (i-1)).map(j => {
//          clauses = clauses + 1
          -i + " " + -j + " 0\n"
        }).mkString("")
      }).mkString("")
    }
    
    def pebbling = {
      (1 to k).foreach(x => {
        out.appendAll(
        (1 to n).map(j => {
          (1 to (n -1)).map(t => {
            proof.nodes(n-j).premises.map(n-proof.nodes.indexOf(_)).map(i => {
//              clauses = clauses + 1
              ((1 to k) diff Seq(x)).map(y => {
                (p(y,i,t) + " ").toString()
              }).mkString("") + (p(x,j,t) + " " + -p(x,j,(t+1)) + " 0\n").toString()
            }) union
            (1 to n).map(i => {
              (1 to (x-1)).map(y => {
//                clauses = clauses + 1
                (p(x,j,t) + " " + -p(x,j,(t+1)) + " " + p(y,i,t) + " " + -p(y,i,(t+1)) + " 0\n").toString()
              })
            }).flatten
          }).flatten
        }).flatten)
      })
    }
    
    out.prepend("p cnf " + (k*n*n) + " " + 0 +"\n")
    println("header written")    
    out.write("c one node per pebble\n" + oneNodePerPebble)
    println("one node per pebble written")
    out.write("c at least 1 init\n" +atLeast1Init)
    println("at least 1 init written")
    out.write("c at most 1 init\n" + atMost1Init)
    println("at most 1 init written")
    out.write("c only axioms init\n" + onlyAxiomsInit)
    println("only axioms init written")
    out.write("c correct pebbling\n")
    pebbling
    println("correct pebbling written")
    out.write("c root pebbled\n" +pebbleRoot)
    println("root pebbled written")
  }
  
  def interpretSAT(filename: String, proof: Proof[N], k: Int) = {
    val n = proof.size
    val in = Input(filename)
    val lines = in.lines
    var permutation: Seq[N] = Seq[N]()
    if (lines.size > 1) {
      val assign = lines.last.split(" ").map(_.toInt)
      val pos = assign.filter(_ > 0)
      pos.foreach(p => {
        val (x,j,t) = intToNode(p,n,k)
        if (t > 1) {
//          println(x,j,t + " -> " + trippleToInt(x,j,t-1,n,k))
          if (assign(trippleToInt(x,j,t-1,n,k) - 1) < 0) {
            permutation = permutation :+ proof.nodes(proof.size - j)
            println("pebble " + intToNode(p,n,k))
          }
        }
        else {
          permutation = permutation :+ proof.nodes(proof.size - j)
          println("pebble " + intToNode(p,n,k))
        }
//        if (t < n) {
//          if (assign(trippleToInt(x,j,t+1,n,k) - 1) < 0) println("unpebble " + intToNode(trippleToInt(x,j,t+1,n,k),n,k))
//        }
      })
//      (0 to (n*k)-1).map(numb => {
//        if (assign(numb) > 0) {
//          println("init " + intToNode(numb,n,k))
//        }
//      })
      println(permutation.size + " ~ " + proof.size)
      new Proof(proof.root, permutation.reverse.toIndexedSeq)
    }
    else {
      println("UNSAT")
      proof
    }
    
  }
  
  def trippleToInt(pebble: Int, node: Int, time: Int, n: Int, k: Int) = pebble + (node-1) * k + (time-1) * k * n
  
  def intToNode(number: Int, n: Int, k: Int) = {
    (((number - 1) % k) + 1,(((number-1) / k) % n) + 1,(((((number - 1) / k / n) % n)) + 1))
  }
  
  def main(args: Array[String]): Unit = {
    val k = 12
    val proof = ProofParserVeriT.read("examples/proofs/VeriT/eq_diamond3.smt2")
    
    
    val out = new FileOutput("experiments/SATPebble2")
    out.clear
    val d = dimacs(k,proof,out)
    
//    out.write(d)
    
    Executer.executeMini("experiments/msat2", "experiments/SATPebble2")
    val outproof = interpretSAT("experiments/msat2", proof,k)
    println(outproof)
    println("SATProof: " + measure(outproof)("space"))
    println("original: " + measure(proof)("space"))
  }
}

object Executer {

  def executeMini(fileName: String, parameters: String): Stream[String] = {
    val call = "minisat " + parameters + " " + fileName
    call.!
    val contents = Process(call).lineStream
    contents
  }
}