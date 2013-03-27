package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.proof.sequent.lk.{Axiom,R}
import at.logic.skeptik.expression.E
import scala.collection.mutable.{HashMap => MMap}


abstract class Split
extends (Proof[N] => Proof[N]) {
  
  def selectVariable(proof: Proof[N]): E
  
  def split(proof: Proof[N], selectedVariable: E): (N,N) = {
    proof foldDown { (node: N, fixedPremises: Seq[(N,N)]) => 
      lazy val (fixedLeftPos,  fixedLeftNeg)  = fixedPremises.head;
      lazy val (fixedRightPos, fixedRightNeg) = fixedPremises.last;
      node match {
        case Axiom(conclusion) => (node,node)
        case R(_,_,aux,_) if aux == selectedVariable => (fixedLeftPos, fixedRightNeg)

        case R(left,right,aux,_) if (fixedLeftPos eq fixedLeftNeg) && (fixedRightPos eq fixedRightNeg) =>
          // I think this case is redundant with the following one and then useless :
          // Neg and Pos being equals implies they're equals to node's premises.
          // Keep the println until it shows something.
          val newNode = if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node
                        else { println("yooups") ; R(fixedLeftPos, fixedRightPos, _ == aux, true) }
          (newNode, newNode)

        case R(left,right,aux,_) =>
          ( if ((left eq fixedLeftPos) && (right eq fixedRightPos)) node else R(fixedLeftPos, fixedRightPos, _ == aux, true),
            if ((left eq fixedLeftNeg) && (right eq fixedRightNeg)) node else R(fixedLeftNeg, fixedRightNeg, _ == aux, true) )
        
        case _ => (node, node)
      }
    }
  }
  
  def applyOnce(p: Proof[N]): Proof[N] = {
    val selectedVariable = selectVariable(p)
    val (left, right) = split(p, selectedVariable)
    val compressedProof: Proof[N] = R(left, right, _ == selectedVariable)
    if (compressedProof.size < p.size) compressedProof else p
  }
}