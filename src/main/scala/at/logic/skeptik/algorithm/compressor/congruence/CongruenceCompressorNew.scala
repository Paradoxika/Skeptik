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
    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val reflMap = MMap[E,N]()
    val axiomEqs = MMap[E,N]()
    val resolveWithMap = MMap[E,MSet[N]]()
    var comp = 0
    var tried = 0
    
    val directory = "$GLOBAL/test5/"
    val filename = "proof_"+proof.hashCode
    val output = new FileOutput(directory + filename)
    val header = "original, produced, theorylemma\n"
    output.write(header)
    val eqNodesLeft = MMap[EqW,N]()
    
    def traversal(node: N, fromPr: Seq[(N,Boolean)]): (N,Boolean) = {
      
      val fixedNode = fixNode(node,fromPr.map(_._1))
      var theorylemma = 
        if (fromPr.isEmpty)
          fixedNode.isInstanceOf[EqAxiom]
        else fromPr.map(_._2).forall(b => b)
      
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
      val resNode = {
        tried = tried + 1
        val eqToMap = rightEqs.map(eq => {
          val con = newCon.addAll(leftEqs).addNode(eq.l).addNode(eq.r).updateLazy
          con.explain(eq.l,eq.r) match {
            case Some(path) => {
              
              
              
              path.toProof match {
                case Some(proof) => {
                  val newSize = proof.root.conclusion.ant.size
                  val oldSize = leftEqs.size
                  
//                  println(newSize == proof.root.conclusion.ant.size)
                  
                  val line = oldSize + ", " + newSize + ", " + theorylemma + "\n"
                  output.write(line)
//                  val fixedProof = Proof(fixedNode)
//                    if (proof.size > fixedProof.size) {
//                      val oldProof = Proof(fixedNode)
//                      println("increasing proof size, length:" + measure(oldProof)("length") + " vs " + measure(proof)("length") +  " trans length:" + measure(oldProof)("transLength") + " vs " + measure(proof)("transLength") + "\n" + Proof(fixedNode) + "\nto\n"+proof)
//                    }
//                    println(proof.root.conclusion.ant.size == path.originalEqs.size)
//                    if (fixedNode.conclusion.size < proof.root.conclusion.size) println("made it bigger: " + fixedNode.conclusion.size +" vs " + proof.root.conclusion.size)
//                    if (fixedNode.conclusion.size == proof.root.conclusion.size) println("stayed the same")
//                    if (fixedNode.conclusion.size > proof.root.conclusion.size) println("got smaller: " + fixedNode.conclusion.size +" vs " + proof.root.conclusion.size)
                  comp = comp + (fixedNode.conclusion.size - proof.root.conclusion.size)
//                    println("compressing")
                  proof.root
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
//      if (resNode.conclusion.suc.size > 1) println("size > 1 in compressor!:\n " + Proof(resNode))
      (resNode,theorylemma)
    }
    
    val newProof = (proof foldDown traversal)._1
    
//    println(newProof)
    
    // Resolve against axioms
    val resProof = newProof.conclusion.suc.foldLeft(newProof)({(A,B) => 
      eqNodesLeft.get(EqW(B)) match { //probably slow
        case Some(node) => {
//          println("blabla")
          R(A,node,B)
        }
        case None => {
          A
        }
      }
    })
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
  }
  
  
  
}