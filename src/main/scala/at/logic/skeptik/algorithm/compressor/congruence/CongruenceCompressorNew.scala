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

object CongruenceCompressorNew extends (Proof[N] => Proof[N]) with fixNodes {
  
  def apply(proof: Proof[N]) = {
    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val notOMap = MMap[EqW,EqW]()
    val axiomEqs = MMap[E,N]()
    val resolveWithMap = MMap[E,MSet[N]]()
    
    val eqNodesLeft = MMap[EqW,N]()
    
    def traversal(node: N, fromPr: Seq[N]): N = {

      val fixedNode = fixNode(node,fromPr)
      
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
      
      val eqToMap = rightEqs.map(eq => {
//        val con = new FibonacciCongruence(eqReferences, new FindTable(), Queue[(E,E)](),WEqGraph(eqReferences)).addAll(leftEqs).addNode(eq.l).addNode(eq.r)
        val con = new ProofTreeCongruence().addAll(leftEqs).addNode(eq.l).addNode(eq.r)
        con.explain(eq.l,eq.r) match {
          case Some(path) => {
            path.toProof match {
              case Some(proof) => proof.root
              case None => fixedNode
            }
          }
          case _ => fixedNode
        }
      })
      if (eqToMap.isEmpty) fixedNode 
      else eqToMap.minBy(_.conclusion.size)
    }
    
    val newProof = proof foldDown traversal
    
    // Resolve against axioms
    val resProof = newProof.conclusion.suc.foldLeft(newProof)({(A,B) => 
      eqNodesLeft.get(EqW(B)) match { //probably slow
        case Some(node) => {
          R(A,node)
        }
        case None => {
          println("no equality for " + B)
          A
        }
      }
    })
    
    println("number of axioms: " + axiomEqs.size)
    resProof.conclusion.ant.foreach(l => {
      println("axiom for " + l + " " + axiomEqs.contains(l))
      println("node to res against fo " + l + " " + resolveWithMap.contains(l))
    })
    resProof
  }
  
  
  
}