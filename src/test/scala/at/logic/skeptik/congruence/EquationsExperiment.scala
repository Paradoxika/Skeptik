//package at.logic.skeptik.congruence
//
//import at.logic.skeptik.parser.ProofParserVeriT
//import at.logic.skeptik.algorithm.congruence
//import at.logic.skeptik.expression.formula._
//import at.logic.skeptik.expression._
//import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
//import at.logic.skeptik.proof._
//import at.logic.skeptik.util.io.Input
//import at.logic.skeptik.algorithm.congruence._
//
//object EquationsExperiment {
//
//  def main(args: Array[String]):Unit = {
//    val reader = new Input("F:/Proofs/QF_UF/QG-classification/QC-classification")
////    val reader = new Input("F:/Proofs/QF_UF/seq_files")
////    val reader = new Input("D:/Paradoxika/Skeptik/prooflists/diamonds")
//    val lines = reader.lines
//    val parser = ProofParserVeriT
////    var percentage: Double = - 1
//    for (singleFile <- lines) {
//      val proof = parser.read(singleFile)
////      println(proof)
////      val axioms = proof.filter(n => n.premises.isEmpty)
////      val y = countTwoRightAndCongruent(proof)
//      val z = checkRedundant(proof)
////      val x = countTrueAxioms(axioms)
////      if (percentage == -1) percentage = x
////      else percentage = (percentage + x)/2
////      println(percentage + " % two right and congruent at: " + singleFile)
////      println(x + " of " + axioms.size + " two right and congruent at: " + singleFile)
//      println(z + " of " + proof.size + " found to be redundant: " + singleFile)
//    }
////    println(percentage)
//    
//  }
//  
//  def countTrueAxioms(axioms: Iterable[N]) = {
//    var count = 0
//    axioms.foreach(node => {
//      if (twoRightAndCongruent(node)) { 
//        count = count + 1
//      }
//    })
//    count
//  }
//  
//  def countTwoRightAndCongruent(proof: Proof[N]) = {
//    var count = 0
//    proof.foreach(node => {
//      if (twoRightAndCongruent(node)) { 
//        count = count + 1
//      }
//    })
////    (count.asInstanceOf[Double] * 100) / proof.size
//    count
//  }
//  
//  def countTwoRight(proof: Proof[N]) = {
//    var count = 0
//    proof.foreach(node => {
//      if (hasTwoRight(node)) {
////        if (node.conclusion.size < 10) println(node.conclusion)
//        count = count + 1
//      }
//    })
////    println(count +" of "+ proof.size + " have 2 eq's right")
////    (count.asInstanceOf[Double] * 100) / proof.size
//    count
//  }
//  
//  def twoRightAndCongruent(node: N): Boolean = {
//    val rightEqs = node.conclusion.suc.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
//    val leftEqs = node.conclusion.ant.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
//    val s = rightEqs.size
//    val twoAndCongruent =
//      if (s > 0) {
//        val con = new Congruence
//        leftEqs.foreach(eq => con.addEquality(eq))
//        con.resolveDeduced
//        rightEqs.exists(eq => {
//          val path = con.explain(eq.function.asInstanceOf[App].argument, eq.argument)
//          val c = path.collectLabels.size
//          val out = c > 0 && c < leftEqs.size
////          if (out) {
////            println(node.conclusion + "\nshorter explanation " + path.collectLabels)
////          }
////          if (!out) println(node.conclusion)
////          println("is congruent: " + eq.function.asInstanceOf[App].argument + ", " + eq.argument + " ? " + c)
//          out
//        })
//      }
//      else false
////      if (s > 0 && leftEqs.size > 0 && !twoAndCongruent) {
////        println(node.conclusion)
////      }
//      twoAndCongruent
//  }
//  
//  def hasTwoRight(node: N): Boolean = {
//    val s = node.conclusion.suc.filter(Eq.?:(_)).size
////    println(s)
//    s > 1
//  }
//  
//  def rightEqs(node: N) = node.conclusion.suc.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
//  
//  def leftEqs(node: N) = node.conclusion.ant.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
//  
//  
//  def checkRedundant(proof: Proof[N]) = {
//  
//    val con = buildGlobalCongruence2(proof)
//    
////    println("congruence graph built")
////    println(con.g)
//    
//    var count = 0
//    
//    proof foldDown checkRedundantTraversal
//    
//        
//    
//    def checkRedundantTraversal(node: N, axiomsUsed: Seq[Set[App]]): Set[App] = {
////      println("process " + node.conclusion)
//      val r = rightEqs(node)
//      val l = leftEqs(node)
////      println("before flattening " + axiomsUsed)
//      val axiomsBefore = axiomsUsed.foldLeft( Set[App]() )( {(A,B) => A union B})
////      println("after flattening " + axiomsBefore)
//      val rSize = r.size
//      val lSize = l.size
//      if (rSize > 0) {
//        if (lSize > 0) {
////          println("before build currentExlp")
//          val currentExpl = axiomsUsed ++: l
////          println("after build currentExlp")
//          if (r.exists(eq => {
////            println("before xplain")
//            //Still have to add left eqns! -> copy con
//            val path = con.explain(eq.function.asInstanceOf[App].argument, eq.argument)
////            println("after xplain")
//            val newExpl = path.collectLabels
//            val c = newExpl.size
//            val out = c > 0 && c < currentExpl.size
////            println("current explanation: " + currentExpl.size + " ~ " + currentExpl)
////            println("new explanation: " + newExpl.size + " ~ " + newExpl)
//            out
//          })) count = count + 1
//          axiomsBefore
//        }
//        else {
//          if (node.premises.size < 2) axiomsBefore.++:(r)
//          else axiomsBefore
//        }
//      }
//      else {
////        println("before flattening")
//        val x = axiomsBefore
////        println("after flattening")
//        x
//      }
//    }
//    count
//  }
//  
//  def buildGlobalCongruence(proof: Proof[N]) = {
//    val con = new Congruence
//    val inputEqNodes = proof.filter(node => node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0 && node.conclusion.suc.forall(Eq.?:(_)))
//    val inputEqs = inputEqNodes.map(node => node.conclusion.suc.last.asInstanceOf[App])
//    inputEqNodes.foreach(node => println(node.getClass()))
////    println("inputEqs: " + inputEqs)
//    inputEqs.foreach(con.addEquality(_))
//    con.resolveDeduced
//    con
//  }
//  
//  def buildGlobalCongruence2(proof: Proof[N]) = {
//    val con = new Congruence
//    
//    proof foldDown traverse
//    
//    def traverse(node: N, premisesFresh: Seq[Boolean]): Boolean = {
////      println(node.conclusion)
//      val fresh = if (premisesFresh.size > 0) premisesFresh.min else true
////      println("fresh? " + fresh)
//      val singleRight = node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0 && node.conclusion.suc.forall(Eq.?:(_))
////      if (singleRight && !fresh) println(node.conclusion + " denied")
//      if (fresh && singleRight) {
//        val eq = node.conclusion.suc.last.asInstanceOf[App]
////        println(eq + " is an original axiom")
//        con.addEquality(eq)
//        false
//      }
//      else fresh
//    }
//    
//    con.resolveDeduced
//    con
//  }
//}