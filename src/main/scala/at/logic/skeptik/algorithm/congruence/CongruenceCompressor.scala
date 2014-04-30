package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable._
import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.congruence._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.proof.sequent.lk.R

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}

object CongruenceCompressor extends (Proof[N] => Proof[N]) with fixNodes {
  
  def apply(proof: Proof[N]): Proof[N] = {
    val (con,eqNodes) = buildGlobalCongruence(proof)
    
    def replaceRedundant(node: N, fromPremises: Seq[(N,Set[App])]): (N,Set[App]) = {
      
      val premiseNodes = fromPremises.map(_._1)
      val premiseAxioms = fromPremises.foldLeft(Set[App]())({(A,B) => A union B._2})
      
      val fixedNodeInit = fixNode(node,premiseNodes)
      
      val rightEqs = fixedNodeInit.conclusion.suc.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
      val leftEqs = fixedNodeInit.conclusion.ant.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
      
//      val r1 = fixedNodeInit.conclusion.suc.filter(Eq.?:(_))
      
      val rS = rightEqs.size
      val lS = leftEqs.size
      
//      println(fixedNodeInit + "\nrS: " + rightEqs + "\nlS " + leftEqs)
      
      if (rS > 0 && lS > 0) {
        
        val localCon = leftEqs.foldLeft(con)({(A,B) => A.addEquality(B)})
        val localConRes = localCon.resolveDeducedQueue
        var tree: Option[EquationTree] = None
        val canBeCompressed = rightEqs.exists(eq => {
          val path = localConRes.explain(eq.function.asInstanceOf[App].argument, eq.argument)
          val newSize = path.allEqs.size
          val oldSize = leftEqs.size + premiseAxioms.size
          val out = newSize > 0 && newSize < oldSize
          if (out) tree = Some(path)
//          println("old: " + oldSize + " vs " + newSize)
//          if (!out && path.toProof.get.size < Proof(node).size) {
//            println("Replacing pays off!")
//            println("path proof: \n" + path.toProof.get)
//            println("\norig proof:\n"+Proof(node))            
//          }
          out
        })
        if (canBeCompressed) {
          println("compressing " + node)
          val path = tree.get
          val pathProof = path.toProof
          pathProof match {
            case Some(proof) => {
              val usedEqs = path.allEqs
              usedEqs.foldLeft((proof.root,Set[App]()))({(A,B) => 
                eqNodes.get(B) match {
                  case Some(node) => (R(A._1,node), A._2 + node.conclusion.suc.last.asInstanceOf[App])
                  case None => A
                }
              })
            }
            case None => (fixedNodeInit,premiseAxioms)
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
    }
    val (newProof, _) = proof foldDown replaceRedundant
    newProof
  }
  
  
  
def buildGlobalCongruence(proof: Proof[N]): (Congruence,MMap[App,N]) = {
    var con = new Congruence
    val eqNodes = MMap[App,N]()
    
    proof foldDown traverse
    
    def traverse(node: N, premisesFresh: Seq[Boolean]): Boolean = {
      val fresh = if (premisesFresh.size > 0) premisesFresh.min else true
      if (fresh) {
        val singleRight = node.conclusion.suc.size == 1 && node.conclusion.ant.size == 0 && node.conclusion.suc.forall(Eq.?:(_))
        if (singleRight) {
          val eq = node.conclusion.suc.last.asInstanceOf[App]
          con = con.addEquality(eq)
          eqNodes += (eq -> node)
          false
        }
        else fresh
      }
      else false
    }
    
    con = con.resolveDeducedQueue
    (con,eqNodes)
  }
}