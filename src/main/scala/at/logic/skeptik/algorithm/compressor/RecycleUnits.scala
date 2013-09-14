package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression.E
import at.logic.skeptik.proof._
import at.logic.skeptik.judgment.SequentLike
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.{HashSet => MSet}

object RecycleUnits extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with fixNodes {
  
  def isUnit[P <: ProofNode[Sequent,P]](n: P) = n.conclusion.width == 1
  
  def apply(proof: Proof[SequentProofNode]) = {
    //stores the unit descendend unit nodes of all proof nodes
    val descUnits = new MMap[SequentProofNode,MSet[SequentProofNode]]
    val ancUnits = new MMap[SequentProofNode,MSet[SequentProofNode]]
    //stores occuring unit nodes in the proof for pivot elements
    val units = new MMap[E,MSet[SequentProofNode]]
    val nodeMap = MMap[Sequent,SequentProofNode]()
    val unitNodes = new MSet[SequentProofNode]
    
    def collectUnits(node: SequentProofNode, children: Seq[SequentProofNode]):SequentProofNode = {
      //collect seen units from children nodes
      val descChild = (new MSet[SequentProofNode] /: children)( (l1,l2) =>
        l1 union descUnits(l2)
      )
      //add unit clause to global set
      if (isUnit(node)) {
        unitNodes += node
        node.conclusion.ant.foreach(l => units(l) = units.getOrElse(l, new MSet[SequentProofNode]) += node )
        node.conclusion.suc.foreach(l => units(l) = units.getOrElse(l, new MSet[SequentProofNode]) += node )
      }
      
      //add unit clause to seen units for this node
      descUnits += (node -> (if (isUnit(node)) descChild + node else descChild))
      node
    }
    
    def getAncUnits(node: SequentProofNode, res: Seq[Unit]):Unit ={
      val ancPremises = (new MSet[SequentProofNode] /: node.premises)( (l1,l2) =>
        l1 union ancUnits(l2)
      )
      if (isUnit(node)) {
        ancPremises += node
      }
      ancUnits(node) = ancPremises
    }

    proof.bottomUp(collectUnits)
    proof foldDown getAncUnits
//    units.foreach(println)
    
    def replaceUnitbyUnit(oldUnit: SequentProofNode, newUnit: SequentProofNode) {
      newUnit.conclusion.ant.foreach(l => {if (units.isDefinedAt(l)) units(l) -= oldUnit; units(l) = units.getOrElse(l, MSet[SequentProofNode]()) + newUnit})
      newUnit.conclusion.suc.foreach(l => {if (units.isDefinedAt(l)) units(l) -= oldUnit; units(l) = units.getOrElse(l, MSet[SequentProofNode]()) + newUnit})
      unitNodes -= oldUnit
      unitNodes += newUnit
      descUnits.foreach(dU => {
        if (dU._2 contains oldUnit) {
          dU._2 -= oldUnit
          dU._2 += newUnit
        }
      })
      ancUnits.foreach(dU => {
        if (dU._2 contains oldUnit) {
          dU._2 -= oldUnit
          dU._2 += newUnit
        }
      })
//      println("updated units:")
//      units.foreach(println)
    }
    
    def replace2(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      if (nodeMap.contains(node.conclusion)) nodeMap(node.conclusion)
      else {
        
        val newNode = fixNode(node,fixedPremises)
        if ((isUnit(newNode)) && (isUnit(node))) {
          replaceUnitbyUnit(node,newNode)
        }
        if (newNode.isInstanceOf[R] || newNode.isInstanceOf[Axiom]) {
          nodeMap += (newNode.conclusion -> newNode)
        }
        ancUnits(newNode) = ancUnits(node)
        descUnits(newNode) = descUnits(node)
        unitNodes.find(u => (u.conclusion subsequentOf newNode.conclusion) && !(fixedPremises contains u) && !descUnits(newNode).contains(u) && ancUnits(u).forall(au => !(descUnits(newNode) contains au))) match {
          case None => newNode
          case Some(u) => {
            u
          }
        }
      }
    }
    
    def replace(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      val newNode = fixNode(node,fixedPremises)
      if ((isUnit(newNode)) && (isUnit(node))) {
        replaceUnitbyUnit(node,newNode)
      }
      val ancPremises = (new MSet[SequentProofNode] /: fixedPremises)( (l1,l2) =>
        l1 union ancUnits(l2)
      )
      if (isUnit(newNode)) {
        ancPremises += newNode
      }
      ancUnits(newNode) = ancPremises
      descUnits(newNode) = descUnits(node)
      node match {
        case R(left, right, pivot, _) => {
          val fixedLeft  = fixedPremises.head
      		val fixedRight = fixedPremises.last
      		//find unit nodes with the current pivot element which are not ancestors of the current node and for which none of its ancestor units are contained in the descendend units of the current node
      		units.getOrElse(pivot,new MSet[SequentProofNode]).find(u => !(fixedPremises contains u) && !descUnits(newNode).contains(u) && ancUnits(u).forall(au => !(descUnits(newNode) contains au))) match {
            //in case there are no such units -> update the node if needed
            case None => {
//              if (node.conclusion.size == 1) println("new root by fixing old: " + node + " new: " + newNode)
              newNode
            }
            //there is a not ancestor unit in the proof using the current pivot
            case Some(u) => {
              if (fixedPremises contains u) {
                println("fixed premises contains " + u)
              }
    //          println("fixed Premises:" )
    //          fixedPremises.foreach(println)
    //          println("u:")
    //          println(u)
              //println(u.conclusion + " contains " + pivot + " suc c: " + u.conclusion.suc.contains(pivot))
              //pivot is negative
              val newNewNode = if (u.conclusion.suc.contains(pivot)) {
//                println("fixing parent " + fixedLeft + " to " + u)
                fixNode(node,pivot,left,right,u,fixedRight)
              }
              //pivot is positive
              else {
//                println("fixing parent " + fixedRight + " by " + u)
                fixNode(node,pivot,left,right,fixedLeft,u)
              }
//              println("replacing " + node + " by " + newNewNode)
              if ((isUnit(newNode)) && (isUnit(newNewNode))) {
                replaceUnitbyUnit(newNode,newNewNode)
              }
              ancUnits(newNewNode) = ancUnits(newNode) union ancUnits(u)
              descUnits(newNewNode) = if (isUnit(newNewNode)) descUnits(newNode) + newNewNode else descUnits(newNode)
              newNewNode
            }
          }
        }
        case _ => newNode
      }
    }
    val out = Proof(proof foldDown replace2)
    if (out.size < proof.size) out else proof
  }
}
