package at.logic.skeptik.congruence

import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.algorithm.congruence
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof._
import at.logic.skeptik.util.io.Input
import at.logic.skeptik.algorithm.congruence._
import scala.collection.mutable.{HashMap => MMap}

object EquationsExperiment {

  def main(args: Array[String]):Unit = {
    val reader = new Input("F:/Proofs/QF_UF/QG-classification/QC-classification")
//    val reader = new Input("F:/Proofs/QF_UF/seq_files")
//    val reader = new Input("D:/Paradoxika/Skeptik/prooflists/diamonds")
    val lines = reader.lines
    val parser = ProofParserVeriT
//    var percentage: Double = - 1
    for (singleFile <- lines) {
      val proof = parser.read(singleFile)
//      println(proof)
//      val axioms = proof.filter(n => n.premises.isEmpty)
//      val y = countTwoRightAndCongruent(proof)
      val z = checkRedundant(proof)
//      val x = countTrueAxioms(axioms)
//      if (percentage == -1) percentage = x
//      else percentage = (percentage + x)/2
//      println(percentage + " % two right and congruent at: " + singleFile)
//      println(x + " of " + axioms.size + " two right and congruent at: " + singleFile)
      println(z + " of " + proof.size + " found to be redundant: " + singleFile)
    }
//    println(percentage)
    
    
//    val proof = ProofParserVeriT.read("D:/Paradoxika/Skeptik/examples/proofs/VeriT/eq_diamond2.smt2")
//    
//    checkRedundant(proof)
  }
  
  def countTrueAxioms(axioms: Iterable[N]) = {
    var count = 0
    axioms.foreach(node => {
      if (twoRightAndCongruent(node)) { 
        count = count + 1
      }
    })
    count
  }
  
  def countTwoRightAndCongruent(proof: Proof[N]) = {
    var count = 0
    proof.foreach(node => {
      if (twoRightAndCongruent(node)) { 
        count = count + 1
      }
    })
//    (count.asInstanceOf[Double] * 100) / proof.size
    count
  }
  
  def countTwoRight(proof: Proof[N]) = {
    var count = 0
    proof.foreach(node => {
      if (hasTwoRight(node)) {
//        if (node.conclusion.size < 10) println(node.conclusion)
        count = count + 1
      }
    })
//    println(count +" of "+ proof.size + " have 2 eq's right")
//    (count.asInstanceOf[Double] * 100) / proof.size
    count
  }
  
  def twoRightAndCongruent(node: N): Boolean = {
    val rightEqs = node.conclusion.suc.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
    val leftEqs = node.conclusion.ant.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
    val s = rightEqs.size
    val twoAndCongruent =
      if (s > 0) {
        val con = new Congruence(MMap[(E,E),App]())
        leftEqs.foreach(eq => con.addEquality(eq))
        con.resolveDeducedQueue
        rightEqs.exists(eq => {
          val path = con.explain(eq.function.asInstanceOf[App].argument, eq.argument)
          val c = if (path.isDefined) path.get.collectLabels.size else 0
          val out = c > 0 && c < leftEqs.size
//          if (out) {
//            println(node.conclusion + "\nshorter explanation " + path.collectLabels)
//          }
//          if (!out) println(node.conclusion)
//          println("is congruent: " + eq.function.asInstanceOf[App].argument + ", " + eq.argument + " ? " + c)
          out
        })
      }
      else false
//      if (s > 0 && leftEqs.size > 0 && !twoAndCongruent) {
//        println(node.conclusion)
//      }
      twoAndCongruent
  }
  
  def hasTwoRight(node: N): Boolean = {
    val s = node.conclusion.suc.filter(Eq.?:(_)).size
//    println(s)
    s > 1
  }
  
  def rightEqs(node: N) = node.conclusion.suc.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
  
  def leftEqs(node: N) = node.conclusion.ant.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
  
  
  def checkRedundant(proof: Proof[N]) = {
  
    val con = buildGlobalCongruence2(proof)
    
//    println("congruence graph built")
//    println(con.g)
    
    var count = 0
    var c = 0
    proof foldDown checkRedundantTraversal
    
       
    
    def checkRedundantTraversal(node: N, fromPremises: Seq[(Set[App],Int)]): (Set[App],Int) = {
//      println("process " + node.conclusion)
      
      val r = rightEqs(node)
      val l = leftEqs(node)
//      println("before flattening " + axiomsUsed)
      
      val children = proof.childrenOf(node).size
      val childrenFromPr = if (fromPremises.isEmpty) 0 else fromPremises.map(_._2).max
      
      val maxChild = 
        if (childrenFromPr < children) {
          children
        }
        else {
          childrenFromPr
        }
      if (children > 30) {
       
//        var c = 0
//        val x = proof.childrenOf(node).forall(ch => {
//          println("child " + " " + c + " premise contains node?: " + ch.premises.contains(node) + " " + ch)
//          c = c + 1
//          println(" ")
//          ch.premises.foreach(println)
//          ch.premises.contains(node)
//        })
         println("has 30 or more children: " + node)
         println(node.getClass())
//         println("all children contain node as premise: " + x)
//        println(node)
      }
      val axiomsBefore = fromPremises.foldLeft( Set[App]() )( {(A,B) => A union B._1})
//      println(c + " node: " + node + " axioms: " + axiomsBefore)
      c = c + 1
      val rSize = r.size
      val lSize = l.size
      val axiomsAfter = if (rSize > 0) {
        if (lSize > 0) {
//          println("before build currentExlp")
          val currentExpl = axiomsBefore ++ l
//          println("after build currentExlp")
          if (r.exists(eq => {
//            println("before xplain")
            //Still have to add left eqns! -> copy con
            val newCon = l.foldLeft(con)({(A,B) => A.addEquality(B)})
            val path = newCon.explain(eq.function.asInstanceOf[App].argument, eq.argument)
//            println("after xplain")
            val c = if (path.isDefined) path.get.collectLabels.size else 0
            val out = c > 0 && c < currentExpl.size
            if (out) {
//              println("current explanation for " + r.mkString(",") + ": " + currentExpl.size + " ~ " + currentExpl)
//              println("new explanation     for " + r.mkString(",") + ": " + newExpl.size + " ~ " + newExpl)
//              println(node + " ~ " + axiomsBefore)
//              println("redundant, maxChild: " + maxChild + " current: " + children)
//              println(Proof(node))
            }
            out
          })) count = count + 1
          axiomsBefore
        }
        else {
          if (axiomsBefore.isEmpty && node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0) {
//            println(node + " adds axiom")
            axiomsBefore.++:(r)
          }
          else axiomsBefore
        }
      }
      else {
//        println("before flattening")
        val x = axiomsBefore
//        println("after flattening")
        x
      }
      (axiomsAfter,maxChild)
    }
    count
  }
  
  def buildGlobalCongruence(proof: Proof[N]) = {
//    val con = new Congruence
    val inputEqNodes = proof.filter(node => node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0 && node.conclusion.suc.forall(Eq.?:(_)))
    val inputEqs = inputEqNodes.map(node => node.conclusion.suc.last.asInstanceOf[App])
    inputEqNodes.foreach(node => println(node.getClass()))
//    println("inputEqs: " + inputEqs)
    val con = inputEqs.foldLeft(new Congruence(MMap[(E,E),App]()))({(A,B) => A.addEquality(B)}).resolveDeducedQueue
    con
  }
  
  def buildGlobalCongruence2(proof: Proof[N]) = {
    var con = new Congruence(MMap[(E,E),App]())
    
    proof foldDown traverse
    
    def traverse(node: N, premisesFresh: Seq[Boolean]): Boolean = {
//      println(node.conclusion)
      val fresh = if (premisesFresh.size > 0) premisesFresh.min else true
//      println("fresh? " + fresh)
      val singleRight = node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0 && node.conclusion.suc.forall(Eq.?:(_))
//      if (singleRight && !fresh) println(node.conclusion + " denied")
      if (fresh && singleRight) {
        val eq = node.conclusion.suc.last.asInstanceOf[App]
//        println(eq + " is an original axiom")
        con = con.addEquality(eq)
        false
      }
      else fresh
    }
    
    con = con.resolveDeducedQueue
    con
  }
}