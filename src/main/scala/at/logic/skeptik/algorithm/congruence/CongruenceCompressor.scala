package at.logic.skeptik.algorithm.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable._
import at.logic.skeptik.proof._
import at.logic.skeptik.algorithm.congruence._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.algorithm.compressor._
import at.logic.skeptik.algorithm.dijkstra._

object CongruenceCompressor extends (Proof[N] => Proof[N]) with fixNodes {
  
  def apply(proof: Proof[N]): Proof[N] = {
    proof.last.conclusion
    proof
  }
  
  def replaceRedundant(node: N, fromPremises: Seq[(N,Map[App,N])]): (N,Map[App,N]) = {
    val fixedNodeInit = fixNode(node,fromPremises.map(_._1))
    
    val rightEqs = fixedNodeInit.conclusion.suc.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])
    val leftEqs = fixedNodeInit.conclusion.ant.filter(Eq.?:(_)).map(f => f.asInstanceOf[App])

    val provedEqs = fromPremises.foldLeft(Map[App,N]())({(A,B) => A ++: B._2})
    
    val rS = rightEqs.size
    val lS = leftEqs.size
    
    val fixedNode = 
      if (rS > 0 && lS > 0) {
        val con = new Congruence
        leftEqs.foreach(eq => con.addEquality(eq))
//        con.resolveDeduced
        var tree: Option[EquationTree] = None
        val canBeCompressed = rightEqs.find(eq => {
          val path = con.explain(eq.function.asInstanceOf[App].argument, eq.argument)
          val c = path.collectLabels.size
          val out = c > 0 && c < leftEqs.size
          if (out) tree = Some(path)
//          if (out) {
//            println(node.conclusion + "\nshorter explanation " + path.collectLabels)
//          }
//          if (!out) println(node.conclusion)
//          println("is congruent: " + eq.function.asInstanceOf[App].argument + ", " + eq.argument + " ? " + c)
          out
        })
        if (canBeCompressed.isDefined) {
          val path = tree.get
          
          fixedNodeInit
        }
        else fixedNodeInit
      }
      else fixedNodeInit
    val newProofs = rightEqs.map(eq => (eq -> fixedNode)).toMap ++: provedEqs
    
    (fixedNode,newProofs)
  }
  
  def pathToProof(path: EquationTree, provedEqs: Map[App,N]) = {
    
  }
}