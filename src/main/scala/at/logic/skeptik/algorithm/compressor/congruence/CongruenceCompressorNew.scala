package at.logic.skeptik.algorithm.compressor.congruence

import at.logic.skeptik.util.io.FileOutput
import at.logic.skeptik.expression.{E,App}
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import at.logic.skeptik.congruence.AbstractCongruence
import at.logic.skeptik.congruence.structure.{EqW,EquationPath}

abstract class CongruenceCompressorNew extends (Proof[N] => Proof[N]) with fixNodes {
  
  
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): AbstractCongruence
  
  def apply(proof: Proof[N]) = {
    
//    System.out.println("compressing with congruence")
    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val reflMap = MMap[E,N]()
//    val resolveWithMap = MMap[E,MSet[N]]()
//    var comp = 0
//    var tried = 0
    
    val directory = "/global/lv70340/AFellner/explsize_13/"
    val filename = this.getClass.getSimpleName + "_proof_"+proof.hashCode
    val output = new FileOutput(directory + filename)
    val header = "original, produced, theorylemma\n"
    output.write(header)
    
    
//    val theoryLemma = MSet[N]();
    val lowTheoryLemma = MSet[N]();
    
    def classifyNodes(node: N, fromPr: Seq[(N,Boolean)]): (N,Boolean) = {
      if (fromPr.isEmpty) (node,node.isInstanceOf[EqAxiom])
      else {
        var theorylemma = fromPr.map(_._2).forall(b => b)
        if (!theorylemma) {
          lowTheoryLemma ++= fromPr.filter(b => b._2).map(_._1)
        }
        (node,theorylemma)
      }
    }
    
    def traversal(node: N, fromPr: Seq[(N,Boolean)]): (N,Boolean) = {
      if (fromPr.isEmpty) (node,node.isInstanceOf[EqAxiom])
      else {
        val fixedNode = fixNode(node,fromPr.map(_._1))
        var theorylemma = fromPr.map(_._2).forall(b => b)
        
        val rightEqs = fixedNode.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
        val leftEqs = fixedNode.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
        
//        if (fixedNode.conclusion.suc.size == 1 && fixedNode.conclusion.ant.size == 0) axiomEqs += (fixedNode.conclusion.suc.last -> fixedNode)
        
//        if (fixedNode.conclusion.suc.size == 1 && fixedNode.conclusion.suc.forall(EqW.isEq(_))) 
//          resolveWithMap.update(fixedNode.conclusion.suc.last, resolveWithMap.getOrElse(fixedNode.conclusion.suc.last, MSet[N]()) += fixedNode)
//        val resNode = if (lowTheoryLemma.contains(node)) {
        val resNode = if (true) {
//          System.out.println(node.conclusion + " is theorylemma");
//          tried = tried + 1
          val con = newCon.addAll(leftEqs)
          val eqToMap = rightEqs.map(eq => {
            val con2 = con.addNode(eq.l).addNode(eq.r).updateLazy
            con2.explain(eq.l,eq.r) match {
              case Some(path) => {
                
                
                
                path.toProof match {
                  case Some(proof) => {
                    val newSize = proof.root.conclusion.ant.size
                    val oldSize = leftEqs.size
                   if ((newSize - oldSize) > 5) {
//                     System.out.println("new: " + proof.root.conclusion + " is longer than old:\n" + fixedNode.conclusion);
                     System.out.println(proof.size + " vs " + Proof(node).size)
                   }
                    val line = oldSize + ", " + newSize + ", " + theorylemma + "\n"
                    output.write(line)
                    
//                    comp = comp + (fixedNode.conclusion.size - proof.root.conclusion.size)
  //                    println("compressing")
                    if (newSize < oldSize || (newSize == oldSize && proof.size < Proof(fixedNode).size)) proof.root
//                    if (proof.size <= Proof(node).size) proof.root
                    else fixedNode
                  }
                  case None => fixedNode
                }
              }
              case _ => fixedNode
            }
          })
          
          val x = if (eqToMap.isEmpty) {
  //            println("reach this")
            fixedNode 
          }
          else eqToMap.minBy(_.conclusion.size)
  //          println(eqToMap.size + " ~ " + x)
          x
        }
        else {
          fixedNode
        }
  //      if (resNode.conclusion.suc.size > 1) println("size > 1 in compressor!:\n " + Proof(resNode))
        (resNode,theorylemma)
      }
    }
//    proof foldDown classifyNodes
//    println(lowTheoryLemma)
    val newProof = (proof foldDown traversal)._1
    
//    println(newProof)
    
    // Resolve against axioms
//    val resProof = newProof.conclusion.suc.foldLeft(newProof)({(A,B) => 
//      eqNodesLeft.get(EqW(B)) match { //probably slow
//        case Some(node) => {
////          println("blabla")
//          R(A,node,B)
//        }
//        case None => {
//          A
//        }
//      }
//    })
    val resProof2 = newProof.conclusion.ant.foldLeft(newProof)({(A,B) => 
      reflMap.get(B) match {
        case Some(node) => R(A,node)
        case None => A
      }
    })
//    println("refls:" + reflMap.mkString(","))
    if (!resProof2.conclusion.isEmpty) println("non empty clause! " + resProof2)
//    resProof
//    println("all eq comp: " + comp + " tried: " + tried)
    DAGify(resProof2)
//    resProof2
  }
  
  
  
}