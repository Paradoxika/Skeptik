package at.logic.skeptik.algorithm.compressor.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable._
import at.logic.skeptik.proof._
import at.logic.skeptik.congruence._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.algorithm.compressor._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}
import at.logic.skeptik.proof.Proof.apply
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import scala.collection.immutable.{HashMap => IMap,Queue}
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import at.logic.skeptik.congruence.Congruence
import at.logic.skeptik.congruence.structure.EquationPath

abstract class CongruenceCompressorNew extends (Proof[N] => Proof[N]) with fixNodes {
  
  def newCon(implicit eqReferences: MMap[(E,E),EqW]): AbstractCongruence
  
  def apply(proof: Proof[N]) = {
    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val notOMap = MMap[EqW,EqW]()
    val axiomEqs = MMap[E,N]()
    val resolveWithMap = MMap[E,MSet[N]]()
    
    val eqNodesLeft = MMap[EqW,N]()
    
    def traversal(node: N, fromPr: Seq[(N,Boolean)]): (N,Boolean) = {
      
      val fixedNode = fixNode(node,fromPr.map(_._1))
      var replaced = fromPr.map(_._2).exists(b => b)
      
      val rightEqs = fixedNode.conclusion.suc.filter(EqW.isEq(_)).map(EqW(_))
      val leftEqs = fixedNode.conclusion.ant.filter(EqW.isEq(_)).map(EqW(_))
      
      val singleLeft = fixedNode.conclusion.suc.size == 0 && fixedNode.conclusion.ant.size == 1 && fixedNode.conclusion.ant.forall(EqW.isEq(_))
      if (singleLeft) {
        val eq = EqW(fixedNode.conclusion.ant.last)
        eqNodesLeft += (eq -> node)
      }
      
      if (fixedNode.conclusion.suc.size == 1 && fixedNode.conclusion.ant.size == 0) axiomEqs += (fixedNode.conclusion.suc.last -> fixedNode)
      
      if (fixedNode.conclusion.suc.size == 1 && fixedNode.conclusion.suc.forall(EqW.isEq(_))) 
        resolveWithMap.update(fixedNode.conclusion.suc.last, resolveWithMap.getOrElse(fixedNode.conclusion.suc.last, MSet[N]()) += fixedNode)
      val resNode = 
        if (replaced) fixedNode
        else {
          val eqToMap = rightEqs.map(eq => {
    //        val con = new FibonacciCongruence(eqReferences, new FindTable(), Queue[(E,E)](),WEqGraph(eqReferences)).addAll(leftEqs).addNode(eq.l).addNode(eq.r)
            val con = newCon.addAll(leftEqs).addNode(eq.l).addNode(eq.r)
//            println("done adding!")
//            val gBefore = con.g
//            if (eq.toString == "((f2 c_3 c_5) = (f2 (f2 c_3 c_3) c_5))") println("found " + eq + " in compressor")
//            println("explaining: " + eq)
            con.explain(eq.l,eq.r) match {
              case Some(path) => {
//                val gAfter = con.g
//                println("done explaining g same: " + (gBefore == gAfter))
                path.toProof match {
                  case Some(proof) => {
    //                if (Proof(fixedNode).size < proof.size && proof.size < 15) println("original:\n"+Proof(fixedNode) + "\nproduced\n"+proof)
    //                if (Proof(fixedNode).size > proof.size) proof.root
    //                else fixedNode
                    replaced = true
                    proof.root
                  }
                  case None => fixedNode
                }
              }
              case _ => fixedNode
            }
          })
          if (eqToMap.isEmpty) fixedNode 
          else eqToMap.minBy(_.conclusion.size)
        }
      (resNode,replaced)
    }
    
    val newProof = (proof foldDown traversal)._1
    
    // Resolve against axioms
    val resProof = newProof.conclusion.suc.foldLeft(newProof)({(A,B) => 
      eqNodesLeft.get(EqW(B)) match { //probably slow
        case Some(node) => {
          R(A,node)
        }
        case None => {
//          println("no equality for " + B)
          A
        }
      }
    })
    if (!resProof.conclusion.isEmpty) println("non empty clause!")
    resProof
  }
  
  
  
}