package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.expression.E
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashSet => MSet}
import scala.collection.immutable.{HashSet => ISet}

abstract class AbstractSubsumption 
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with fixNodes {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode]
}

trait LeftRight {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode] = proof
}
trait RightLeft {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode] = new Proof(proof.root,false)
}

abstract class OldTopDownSubsumption extends AbstractSubsumption {
  def apply(inputproof: Proof[SequentProofNode]) = {
    val proof = setTraverseOrder(inputproof)
    val nodeMap = new MMap[Sequent,SequentProofNode]
    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
        val subsumer = nodeMap.find( A => A._1.subsequentOf(node.conclusion))
        val subsMap = subsumer.map(a => a._2)
        
        subsMap.getOrElse({
          val newNode = fixNode(node,fixedPremises)
          nodeMap += (newNode.conclusion -> newNode)
          newNode
        })
      })
    })
  }
}

abstract class TopDownSubsumption extends AbstractSubsumption {
  
  def apply(inputproof: Proof[SequentProofNode]) = {
    val proof = setTraverseOrder(inputproof)
    var clauseTree:ClauseTree = EmptyClauseTree()
    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
//      println(clauseTree)
      
      val clauseTreeBefore = clauseTree
      val (newClauseTree,cltNode) = clauseTree.checkSubsumed(new NodeWithIterators(node))
//      println(cltNode + " subsumes " + node)
      if (cltNode eq node) { //no subsumer
        val newNode = fixNode(node,fixedPremises)
        if (newNode eq node) {
          clauseTree = newClauseTree
          node
        }
        else {
          val (newClauseTree2,cltNode2) = clauseTree.checkSubsumed(new NodeWithIterators(newNode))
          clauseTree = newClauseTree2
          newNode
        }
      }
      else {
//        println("there")
//        clauseTree = newClauseTree
        cltNode
      }
      })
    })
  }
}

object OldTDS extends OldTopDownSubsumption with LeftRight

object TopDownLeftRightSubsumption extends TopDownSubsumption with LeftRight

object TopDownRightLeftSubsumption extends TopDownSubsumption with RightLeft

abstract class BottomUpSubsumption extends AbstractSubsumption {
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean
  def apply(inputproof: Proof[SequentProofNode]) = {
    val replaceNodes = new MMap[SequentProofNode,SequentProofNode]
    val nodeMap = new MSet[SequentProofNode]
    
    def collect(node: SequentProofNode, results: Seq[Unit]):Unit = {
      val subsumed = nodeMap.find( A => (A.conclusion subsequentOf node.conclusion) && (notAncestor(A,node)))
      subsumed match {
        case None => nodeMap += node
        case Some(u) => {
//          println(u + " replaces <collect> " + node)
          replaceNodes(node) = u
        }
      }
    }
  
    def replace(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]):SequentProofNode = {
      if (replaceNodes.isDefinedAt(node)) {
        val replacement = replaceNodes(node)
//        println(replacement + " replaces <replace> " + node)
      }
      replaceNodes.getOrElse(node,fixNode(node,fixedPremises))
    }
    val proof = setTraverseOrder(inputproof)

    proof bottomUp collect
//    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
//      if (replaceNodes.isDefinedAt(node)) println("bla")
//      replaceNodes.getOrElse(node,fixNode(node,fixedPremises))
//    })})
    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
      
      replaceNodes.getOrElse(node,{fixNode(node,fixedPremises)})
    })})
  }
}

abstract class BottomUpSubsumptionTime extends BottomUpSubsumption {
  val ancestors = new MMap[SequentProofNode,ISet[SequentProofNode]]
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean = {
    !(ancestors.getOrElse(node, {Proof(node) foldDown collectAncestors; ancestors(node)}) contains ancestor)
  }
  
  def collectAncestors(node: SequentProofNode, premises: Seq[SequentProofNode]):SequentProofNode = {
    ancestors(node) = (ISet(node) /: premises){ (l1,l2) =>
      l1 union ancestors(l2)
    }
//    print("#ancestors of " + node + " " + ancestors(node).size + "\n")
    //ancestors(node).foreach(println)
    node
  }
}

object BottomUpLeftRightSubsumptionTime extends BottomUpSubsumptionTime with LeftRight
object BottomUpRightLeftSubsumptionTime extends BottomUpSubsumptionTime with RightLeft

abstract class BottomUpSubsumptionMemory extends BottomUpSubsumption {
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean = {
    !(node existsAmongAncestors {_ eq ancestor})
  }
}

object BottomUpLeftRightSubsumptionMemory extends BottomUpSubsumptionMemory with LeftRight
object BottomUpRightLeftSubsumptionMemory extends BottomUpSubsumptionMemory with RightLeft

abstract class AxiomSubsumption extends AbstractSubsumption {
  def apply(inputproof: Proof[SequentProofNode]) = {
    val proof = setTraverseOrder(inputproof)
    val axioms = MMap[Sequent,SequentProofNode]()
    Proof(proof foldDown { (node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => node match {
      case Axiom(conclusion) => {
        val subsumed = axioms.find(A => A._1 subsequentOf conclusion)
        val subsMap = subsumed.map(A => A._2)
        subsMap.getOrElse({axioms += (conclusion -> node); node})
      }
      case R(left, right, pivot, _) => fixNode(node,pivot,left,right,fixedPremises)
      case _ => node
    }})
  }
}

object LeftRightAxiomSubsumption extends AxiomSubsumption with LeftRight
object RightLeftAxiomSubsumption extends AxiomSubsumption with RightLeft

//Stores Proof nodes together with iterators over the literals occuring in the conclusion sequent
//copy method is to leave the iterators as they are when traversing a ClauseTree (which should be immutable)
class NodeWithIterators(val nodeI: SequentProofNode, sucIteratorI: Option[Iterator[E]], antIteratorI: Option[Iterator[E]]) {
  val node = nodeI
  var sucIterator = if (sucIteratorI.isDefined) sucIteratorI.get else node.conclusion.suc.iterator
  var antIterator = if (antIteratorI.isDefined) antIteratorI.get else node.conclusion.ant.iterator
  def this(node: SequentProofNode) = this(node,None,None)
  def copy:NodeWithIterators = {
    val (itS1,itS2) = sucIterator.duplicate
    sucIterator = itS1
    val (itA1,itA2) = antIterator.duplicate
    antIterator = itA1
    new NodeWithIterators(node,Some(itS2),Some(itA2))
  }
}

//Represents either a positive or negative variable
//isContainedIn method checks wether the positive/negative variable is in the antecedent/succedent resp. of a SequentProofNode
class Literal(variableI: E, posI: Boolean) {
  val variable = variableI
  val pos = posI
  def isContainedIn(node: NodeWithIterators):Boolean = {
    if (pos) node.node.conclusion.ant contains variable
    else node.node.conclusion.suc contains variable
  }
  override def toString:String = (if(pos) "+" else "-")+ variable
  override def equals(obj: Any) = obj.isInstanceOf[Literal] && (obj.asInstanceOf[Literal].pos == this.pos) && (obj.asInstanceOf[Literal].variable eq this.variable)
}

//ClauseTree is a binary tree structure to store SequentProofNodes according to the literals they contain.
//It allows for a fast check (at most linear in the size of the sequent) if a subsuming Sequent was visited earlier in the proof traversal.
//Real nodes (with two parents) of these trees are represented by a literal and their two parents contain SequentProofNodes that contain/don't contain this literal.
//Parent nodes can also be empty, which indicates that no Sequent was entered yet with that combination of literals contained/not contained.
//Leafs are represented by a NodeWithIterators object that was so far the only node that was inserted in the current literal contain/not contain path.
//The iterators of this object indicate if the leaf can be split further if needed.
//The checkSubsumed traverses the tree down according to the containment of the splitting literals until either a leaf or an empty branch is visited.
abstract class ClauseTree {
  val in: Option[ClauseTree]
  val notIn: Option[ClauseTree]
  def checkSubsumed(node: NodeWithIterators):(ClauseTree,SequentProofNode)
  override def toString: String
}

case class EmptyClauseTree() extends ClauseTree {
  val in = None:Option[ClauseTree]
  val notIn = None:Option[ClauseTree]
  def checkSubsumed(node: NodeWithIterators):(ClauseTree,SequentProofNode) = {
    (ClauseTreeLeaf(node),node.node)
  }
}

case class ClauseTreeLeaf(leafNode: NodeWithIterators) extends ClauseTree {
  val in = None:Option[ClauseTree]
  val notIn = None:Option[ClauseTree]
  def checkSubsumed(node: NodeWithIterators):(ClauseTree,SequentProofNode) = {
    if (((!leafNode.sucIterator.hasNext) && (!leafNode.antIterator.hasNext)) || (leafNode eq node)) {
//      println(leafNode.node + " subsumes " + node.node)
      (this,leafNode.node)
    }
    else { //either sucIterator or antIterator have next in this case
      val leafCopy = leafNode.copy
      val next = if (leafCopy.antIterator.hasNext) new Literal(leafCopy.antIterator.next,true) else new Literal(leafCopy.sucIterator.next,false) //if antIterator has no next sucIterator has to have next
      ClauseTreeNode(next,leafCopy,node).checkSubsumed(node)
    }
  }
  override def toString: String = "["+leafNode.node.toString+"]"
}
case class ClauseTreeNode(literal: Literal, node1: NodeWithIterators, node2: NodeWithIterators , inI: Option[ClauseTree] = None, notInI: Option[ClauseTree] = None) extends ClauseTree {
//  val in = Some(new ClauseTreeLeaf(node1))
//  val notIn = None
  def this(literal: Literal, inI: Option[ClauseTree], notInI: Option[ClauseTree]) = this(literal,null,null,inI,notInI)
  val (in,notIn) = if (inI.isDefined || notInI.isDefined) {
    (inI,notInI)
  }
  else {
//    println(inI + " ~ " + notInI)
    val check2 = if (literal.pos) {
//      println(node2)
      node2.node.conclusion.ant
    }
    else node2.node.conclusion.suc
    check2 contains literal.variable match {
      case true => {
        val node1Copy = node1.copy
        val next = if (node1Copy.antIterator.hasNext) Some(new Literal(node1Copy.antIterator.next,true)) else if (node1Copy.sucIterator.hasNext) Some(new Literal(node1Copy.sucIterator.next,false)) else None:Option[Literal]
        val i = next match {
          case None => ClauseTreeLeaf(node1Copy)
          case Some(l) => ClauseTreeNode(l,node1Copy,node2)
        }
        (Some(i),None:Option[ClauseTree])
      }
      case false => {
        (Some(ClauseTreeLeaf(node1)),Some(ClauseTreeLeaf(node2)))
      }
    }
  }
//  if (inI.isDefined || notInI.isDefined) {
//    println("node created with existing branches: " + this)
//  }
  
  def checkSubsumed(node: NodeWithIterators):(ClauseTree,SequentProofNode) = {
    if(literal.isContainedIn(node)) {
      val result = in.get.checkSubsumed(node)
//      println("result from pos. branch: " + in + " --> " + result)
      val b = (new ClauseTreeNode(literal,Some(result._1),this.notIn),result._2)
//      println("back: " + b)
      b
    }
    else {
//      if (!notIn.isDefined) println("notIn not defined " + node.node + " lteral: " + literal + " in " + in)
      if (notIn.isDefined) {
        val result = notIn.get.checkSubsumed(node)
        //      println("result from neg. branch: " + notIn + " --> " + result)
        val b = (new ClauseTreeNode(literal,this.in,Some(result._1)),result._2)
  //      println("back: " + b)
        b
      }
      else {
        (new ClauseTreeNode(literal,this.in,Some(ClauseTreeLeaf(node))),node.node)
      }
    }
    
  }
  override def toString: String = "[{"+literal+"}+ " + in.getOrElse("*") + " | - " + notIn.getOrElse("*") + "]"
}