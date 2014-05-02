package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable._
import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.congruence._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.algorithm.compressor._

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}

object CongruenceCompressor extends (Proof[N] => Proof[N]) with fixNodes {
  
  def apply(proof: Proof[N]): Proof[N] = {
    val (con,eqNodesLeft,eqNodesRight) = buildGlobalCongruence(proof)
    
    val premiseAxiomMap = MMap[N,Set[App]]()
//    var first = true
    def replaceRedundant(node: N, fromPremises: Seq[(N,Set[App],Boolean)]): (N,Set[App],Boolean) = {
      println("processing " + node)
      val inputDerived = 
        if (node.isInstanceOf[Axiom]) true 
        else 
          if (fromPremises.size > 0) fromPremises.map(_._3).max else false
      val premiseNodes = fromPremises.map(_._1)
      
      
      val fixedNodeInit = fixNode(node,premiseNodes)
      val premiseAxioms = premiseAxiomMap.getOrElseUpdate(fixedNodeInit, {
        val premiseAxiomsTmp = fromPremises.foldLeft(Set[App]())({(A,B) => A union B._2})
        if (node == fixedNodeInit) premiseAxiomsTmp
        else premiseAxiomsTmp.filter(Proof(fixedNodeInit).nodes.contains(_))
      })
      
      val rightEqs = fixedNodeInit.conclusion.suc.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
      val leftEqs = fixedNodeInit.conclusion.ant.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
      
//      val r1 = fixedNodeInit.conclusion.suc.filter(Eq.?:(_))
      
      val rS = rightEqs.size
      val lS = leftEqs.size
      
//      println(fixedNodeInit + "\nrS: " + rightEqs + "\nlS " + leftEqs)
      
      val (resNode,resAxioms) = if (rS > 0 && lS > 0 && inputDerived) {
        
        val localCon = leftEqs.foldLeft(con)({(A,B) => A.addEquality(B)})
        val localConRes = localCon.resolveDeducedQueue
        var tree: Option[EquationTree] = None
        val canBeCompressed = rightEqs.exists(eq => {
          val (l,r) = (eq.function.asInstanceOf[App].argument,eq.argument)
          val localConFinal = localConRes.addNode(l).addNode(r)
          val path = localConFinal.explain(l,r)
          path match {
            case Some(p) => {
              val newSize = p.originalEqs.size
              val oldSize = leftEqs.size + premiseAxioms.size
              if (newSize < oldSize) {
                tree = path
                true
              }
              else false
            }
            case None => false
          }
        })
        if (canBeCompressed) {
          
          val path = tree.get
//          println("proofing " + (path.firstVert,path.lastVert) + " from " + path.originalEqs)
//          println("path: " + path)
          val pathProof = path.toProof
          val usedEqs = path.originalEqs
          pathProof match  {
            case Some(proof) if (usedEqs.size < fixedNodeInit.conclusion.ant.size) => { //try without the if here ~ maybe reveal more bugs
              println("before " + fixedNodeInit)
//              println(usedEqs.mkString(",") == proof.root.conclusion.ant.mkString(","))
              if (!(usedEqs.toSet.diff(proof.root.conclusion.ant.toSet).isEmpty &&  proof.root.conclusion.ant.toSet.diff(usedEqs.toSet).isEmpty)) {
//                println(usedEqs + " differs from \n" + proof.root.conclusion.ant)
              }
              if (usedEqs.size > fixedNodeInit.conclusion.ant.size) {
//                println("compressing, but producing longer expl")
              }
              val (resNode, resAxioms) = usedEqs.foldLeft((proof.root,Set[App]()))({(A,B) => 
                eqNodesRight.get(B) match {
                  case Some(node) => (R(A._1,node), A._2 + node.conclusion.suc.last.asInstanceOf[App])
                  case None => A
                }
              })
              println("after  " + resNode)
              (resNode,resAxioms)
            }
            case _ => (fixedNodeInit,premiseAxioms)
          }
        }
        else (fixedNodeInit,premiseAxioms)
      }
      else {
        if (rS == 1 && lS == 0) {
          (fixedNodeInit,premiseAxioms + rightEqs.last)
        }
        else (fixedNodeInit,premiseAxioms)
      }
      (resNode,resAxioms,inputDerived)
    }
    val (newProof, _,_) = proof foldDown replaceRedundant
    val resProof = newProof.conclusion.suc.foldLeft(newProof)({(A,B) => 
      eqNodesLeft.get(B.asInstanceOf[App]) match {
        case Some(node) => {
          R(A,node)
        }
        case None => {
          println("no equality for " + B)
          A
        }
      }
    })

    DAGify(resProof)
  }
  
  
  
def buildGlobalCongruence(proof: Proof[N]): (Congruence,MMap[App,N],MMap[App,N]) = {
    var con = new Congruence
    val eqNodesLeft = MMap[App,N]()
    val eqNodesRight = MMap[App,N]()
    
    proof foldDown traverse
    
    def traverse(node: N, premisesFresh: Seq[(Boolean,Boolean)]): (Boolean,Boolean) = {
      val freshLeft = if (premisesFresh.size > 0) premisesFresh.map(_._1).min else true
      val freshRight = if (premisesFresh.size > 0) premisesFresh.map(_._2).min else true
      val freshLeftOut = if(true) {
        val singleLeft = node.conclusion.suc.size == 0 && node.conclusion.ant.size == 1 && node.conclusion.ant.forall(Eq.?:(_))
        if (singleLeft) {
          val eq = node.conclusion.ant.last.asInstanceOf[App]
          eqNodesLeft += (eq -> node)
          false
        }
        else true
      }
      else false
      val freshRightOut = if (freshRight) {
        val singleRight = node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0 && node.conclusion.suc.forall(Eq.?:(_))
        if (singleRight) {
          val eq = node.conclusion.suc.last.asInstanceOf[App]
          con = con.addEquality(eq)
          eqNodesRight += (eq -> node)
          false
        }
        else true
      }
      else false
      (freshLeftOut,freshRightOut)
    }
    
    con = con.resolveDeducedQueue
    println("eqNodesLeft in bGC " + eqNodesLeft.mkString(","))
    (con,eqNodesLeft,eqNodesRight)
  }
}