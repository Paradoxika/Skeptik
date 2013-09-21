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

/**
 * Basic subsumption class
 * Uses the fixNodes traits defined in at.logic.skeptik.algorithm.compressor package object
 * Abstract method for setting the traverse order
 */
abstract class AbstractSubsumption 
extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with fixNodes {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode]
}

/**
 * Trait for the default order of the proof
 * At the moment, the default order is left premise -> right premise -> node
 */
trait LeftRight {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode] = proof
}

/**
 * Trait for a right premise -> left premise -> node order
 * The setTraverseOrder method reconstructs the proof using this order.
 * This needs one traversal of the whole proof.
 * Possibly a soft version of using another order would be preferable to reconstructing the proof.
 */
trait RightLeft {
  def setTraverseOrder(proof: Proof[SequentProofNode]):Proof[SequentProofNode] = new Proof(proof.root,false)
}

/**
 * Naive top-down subsumption storing the (not subsumed) visited nodes in a map with their conclusion sequents.
 * At every node the node-map is searched for a subsuming node. (Where node1 is said to subsume node2 iff their conlcusion sequents do so)
 * If there is a subsuming node, then the current node is replaced by that one.
 * Otherwise the current node is stored in the map with its conclusion sequents. 
 */
abstract class NaiveTopDownSubsumption extends AbstractSubsumption {
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

/**
 * New version of top-down subsumption using the clause tree structure defined below for storing nodes and checking for subsuming ones.
 */

abstract class TopDownSubsumption extends AbstractSubsumption {
  
  def apply(inputproof: Proof[SequentProofNode]) = {
    val proof = setTraverseOrder(inputproof)
    //Initialise the variable clauseTree with an empty clause tree
    var clauseTree:ClauseTree = EmptyClauseTree()
    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
      //As described below, the checkSubsumed method delivers a new clause Tree and a node, which is either subsuming the current one or is the current one itself if no subsumer is stored in the clause tree
      val (newClauseTree,cltNode) = clauseTree.checkSubsumed(new NodeWithIterators(node))
      if (cltNode eq node) { //no subsumer was found in the clause tree
        val newNode = fixNode(node,fixedPremises)
        if (newNode eq node) { //Fixing did not result in a new node
          clauseTree = newClauseTree
          node
        }
        else { //the current node was fixed to a new node
          //This new node has to be inserted into the clause tree by checking for a subsumer
          val (newClauseTree2,cltNode2) = clauseTree.checkSubsumed(new NodeWithIterators(newNode))
          clauseTree = newClauseTree2
          //So far, I have not experienced any difference when replacing newNode with cltNode2 here.
          //This means that newNode never has a subsumer
          newNode
        }
      }
      else { //A subsumer was found and is returned. The clause tree is unchanged.
        cltNode
      }
      })
    })
  }
}

object OldTDS extends NaiveTopDownSubsumption with LeftRight

object TopDownLeftRightSubsumption extends TopDownSubsumption with LeftRight

object TopDownRightLeftSubsumption extends TopDownSubsumption with RightLeft


/**
 * Naive bottom-up subsumption.
 * Bottom-up subsumption uses two traversals.
 * The first, in a bottom-up fashion, searches for subsuming nodes among all the nodes that have been visited earlier.
 * The second, in a top-down fashion, fixes the proof and does replaces nodes according to the replacements collected in the first traversal.
 * There is still a problem with how these two traversals work in combination.
 * The order for a top-down traversal is not preserved when applying replacements, that were found in a bottom-up fashion.
 * This has several negative effects. For example one replacement might be ok (subsuming + not ancestor) before another replacement is applied, 
 * but the ancestor condition might be violated afterwards.
 * Also some nodes might be get fixed, but get new ancestors, because of the application of some replacement and should therefore be fixed again.
 * Solving this issue is not trivial. A mutable proof structure might help. A jumping version of proof traversal does not resolve the issue.
 * There is no version of bottom-up subsumption yet that uses the clause tree structure.
 * This is because while checking subsumption, the ancestor check is not done in the clause tree.
 * The clause tree structure probably has to be extended to be able to do additional checks while searching for a subsuming clause.
 */
abstract class BottomUpSubsumption extends AbstractSubsumption {
  //Abstract method checking if one node is an ancestor of another node
  //true if the second argument is not an ancestor of the first argument
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean
  def apply(inputproof: Proof[SequentProofNode]) = {
    
    //Map for replacements that have been collected in the bottom-up traversal
    val replaceNodes = new MMap[SequentProofNode,SequentProofNode]
    
    //Set of nodes that have been visited
    val nodeSet = new MSet[SequentProofNode]
    
    def collect(node: SequentProofNode, results: Seq[Unit]):Unit = {
      val subsumed = nodeSet.find( A => (A.conclusion subsequentOf node.conclusion) && (notAncestor(A,node)))
      subsumed match {
        //No replacement has been found and therefore the node is added to the set of visited nodes
        case None => nodeSet += node
        //A replacement is found and stored in the map
        //The original node is not stored in the node-set, because it is not desireable to replace another node by a replaced node
        case Some(u) => {
          replaceNodes(node) = u
        }
      }
    }
    val proof = setTraverseOrder(inputproof)

    proof bottomUp collect
    
    //Nodes are replaced or fixed in a top-down traversal
    Proof(proof foldDown { ((node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) => {
      replaceNodes.getOrElse(node,{fixNode(node,fixedPremises)})
    })})
  }
}

/**
 * Version of bottom-up subsumption, which favors computation speed over memory consumption.
 * This version keeps track of the ancestor nodes of every node in form of maps with nodes as keys and sets of nodes as values.
 * Whenever the notAncestor method is called, the ancestors are either computed or read if they have already been computed. 
 * It is then checked if the node of interest is contained in the resulting set.
 */
abstract class BottomUpSubsumptionTime extends BottomUpSubsumption {
  val ancestors = new MMap[SequentProofNode,ISet[SequentProofNode]]
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean = {
    !(ancestors.getOrElse(node, {Proof(node) foldDown collectAncestors; ancestors(node)}) contains ancestor)
  }
  
  //The ancestors of a node are computed as a union of all ancestors of the premises plus the node itself
  def collectAncestors(node: SequentProofNode, premises: Seq[SequentProofNode]):SequentProofNode = {
    ancestors(node) = (ISet(node) /: premises){ (l1,l2) =>
      l1 union ancestors(l2)
    }
    node
  }
}

object BottomUpLeftRightSubsumptionTime extends BottomUpSubsumptionTime with LeftRight
object BottomUpRightLeftSubsumptionTime extends BottomUpSubsumptionTime with RightLeft

/**
 * Version of bottom-up subsumption, which does not need so much memory, but takes more time.
 * The ancestor check is done by comparing the premises of the first argument recursively to the second argument.
 * This is done in such a way, that no comparisons are done twice.
 */
abstract class BottomUpSubsumptionMemory extends BottomUpSubsumption {
  def notAncestor(node: SequentProofNode, ancestor: SequentProofNode):Boolean = {
    !(node existsAmongAncestors {_ eq ancestor})
  }
}

object BottomUpLeftRightSubsumptionMemory extends BottomUpSubsumptionMemory with LeftRight
object BottomUpRightLeftSubsumptionMemory extends BottomUpSubsumptionMemory with RightLeft

/**
 * Axiom subsumption is a special case of top-down subsumption, where only Axioms are stored as possible replacements for other nodes.
 * So far it does not show satisfying compression results and has therefore not been investigated further.
 */
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

/**
 * A structure, which stores proof nodes together with iterators over the literals occuring in the conclusion sequent.
 * Because the clauseTree structure is immutable and the iterators are called when searching for a subsuming node, 
 * the iterators have to be copied whenever a new search is started.
 * 
 * The class has its own hasNext and next functions, that combine the hasNext and next functions from the iterators of the antecedent and succedent of the conclusion sequent
 */
class NodeWithIterators(val nodeI: SequentProofNode, sucIteratorI: Option[Iterator[E]], antIteratorI: Option[Iterator[E]]) {
  val node = nodeI
  var sucIterator = if (sucIteratorI.isDefined) sucIteratorI.get else node.conclusion.suc.iterator
  var antIterator = if (antIteratorI.isDefined) antIteratorI.get else node.conclusion.ant.iterator
  def this(node: SequentProofNode) = this(node,None,None)
  
  def hasNext = sucIterator.hasNext || antIterator.hasNext
  def next = if (sucIterator.hasNext) new Literal(sucIterator.next,true) else new Literal(antIterator.next,false)
  
  //The copy method returns a new object of this class with the iterators set to where they currently are
  //The iterators of the object itself are updated to duplicates of the current one and essentially stay as they are
  def copy:NodeWithIterators = {
    val (itS1,itS2) = sucIterator.duplicate
    sucIterator = itS1
    val (itA1,itA2) = antIterator.duplicate
    antIterator = itA1
    new NodeWithIterators(node,Some(itS2),Some(itA2))
  }
}

/**
 * A structure that represents either a positive or negative variable
 */
class Literal(variableI: E, posI: Boolean) {
  val variable = variableI
  val pos = posI
  //Checks wether the positive/negative variable is in the succedent/antecedent resp. of a conclusion sequent of a SequentProofNode
  def isContainedIn(node: NodeWithIterators):Boolean = {
    if (pos) node.node.conclusion.suc contains variable
    else node.node.conclusion.ant contains variable
  }
  override def toString:String = (if(pos) "+" else "-")+ variable
  override def equals(obj: Any) = obj.isInstanceOf[Literal] && (obj.asInstanceOf[Literal].pos == this.pos) && (obj.asInstanceOf[Literal].variable eq this.variable)
}

/**
 * ClauseTree is a binary tree structure to store SequentProofNodes according to the literals they contain.
 * It's main idea is to speed up the search for a subsuming clause that was stored earlier in the structure.
 * Each non-leaf node branches the tree according to one literal and splits inserted SequentProofNodes according to whether they contain or not contain that literal.
 * Such a non-leaf node can have empty (represented by the Option None) parents, 
 * which indicate that no SequentProofNode with that combination of literals contained/not contained has been entered into the structure yet.
 * Leafs are represented by a NodeWithIterators object that was so far the only node that was inserted in the current literal contain/not contain path.
 * The iterators of this object indicate if the leaf can be split further if needed or if the ultimate place for this SequentProofNode has been found.
 * 
 * Possible future extensions:
 * Add additional criteria when a subsuming node is accepted, for example it's not an ancestor
 * Change it into a ternary tree and split according to variables and not literals in the following way:
 * - The variable is contained positively
 * - The variable is contained negatively
 * - The variable is not contained at all
 */
abstract class ClauseTree {
  val in: Option[ClauseTree]
  val notIn: Option[ClauseTree]
  /**
   * This method is the heart of the clauseTree structure.
   * It serves two puroposes:
   * Find an earlier inserted SequentProofNode that subsumes the SequentProofNode of question.
   * If no subsuming SequentProofNode was found, insert the SequentProofNode of question into the structure.
   * 
   * It does this by traversing the tree down according to the containment of the splitting literals until either a leaf that can not be split further or an empty branch is found.
   */
  def checkSubsumed(node: NodeWithIterators):(ClauseTree,SequentProofNode)
  override def toString: String
}

/**
 * EmpyClauseTree represents the initial situation of a clauseTree.
 * The call for checkSubsumed simply returns a new ClauseTreeLeaf represented by the SequentProofNode of question.
 */
case class EmptyClauseTree() extends ClauseTree {
  val in = None:Option[ClauseTree]
  val notIn = None:Option[ClauseTree]
  def checkSubsumed(node: NodeWithIterators):(ClauseTree,SequentProofNode) = {
    (ClauseTreeLeaf(node),node.node)
  }
}

/**
 * A ClauseTreeLeaf represents a leaf of a ClauseTree.
 * There can occur two situations:
 * - The stored node is split completely according to its contained literals
 * - The stored node can be split further
 * 
 * An issue is that if a node is stored as a leaf, its iterators will always be at the beginning, even tough some literals have already been checked for containment
 * One can not simply move the iterator whenever a splitting decision is made, since the literals don't necessarily come in the right order
 * An attempt that I implemented that stores the literals that have already been seen upwards and builds its own iterator slowed the whole process down alot
 */
case class ClauseTreeLeaf(leafNode: NodeWithIterators) extends ClauseTree {
  val in = None:Option[ClauseTree]
  val notIn = None:Option[ClauseTree]
  
  /**
   * If the stored node is split completely, then the node of question is subsumed by this node, because both nodes are on the same contained/not contained path 
   * and the stored node does not contain any more literals, while the node of question might still contain additional ones.
   * 
   * If the stored node can be split further, then a new ClauseTreeNode is created with the next literal returned by the iterators of the stored 
   */
  def checkSubsumed(node: NodeWithIterators):(ClauseTree,SequentProofNode) = {
    if (!(leafNode.hasNext) || (leafNode.node eq node.node)) { //Stored node is split completely
      (this,leafNode.node)
    }
    else { //Stored node can be split further --> either sucIterator or antIterator have next in this case
      val copyNode = leafNode.copy
      val next = copyNode.next
      ClauseTreeNode(next,copyNode,node).checkSubsumed(node)
    }
  }
  override def toString: String = "["+leafNode.node.toString+"]"
}

/**
 * A ClauseTreeNode represents an internal node in the ClauseTree
 * It has two parents, representing subtrees that contain/do not contain the literal that is used to split this node.
 * A ClauseTreeNode can either be created by passing two NodeWithIterators - objects and actually performing the splitting, or simply by passing the two branches.
 */
case class ClauseTreeNode(literal: Literal, node1: NodeWithIterators, node2: NodeWithIterators , inI: Option[ClauseTree] = None, notInI: Option[ClauseTree] = None) extends ClauseTree {
  //An alternative constructor that simply overtakes two branches
  //Especially this constructor is used when one of the branches is being updated by calls of the checkSubsumed method
  def this(literal: Literal, inI: Option[ClauseTree], notInI: Option[ClauseTree]) = this(literal,null,null,inI,notInI)
  
  //If one of the two branches are defined, then they are simply copied and no other splitting is calculated
  val (in,notIn) = if (inI.isDefined || notInI.isDefined) {
    (inI,notInI)
  }
  //In this part, the splitting is calculated
  else {
    //The to be split literal has to be searched for in the node of question (node2)
    val check = if (literal.pos) node2.node.conclusion.suc else node2.node.conclusion.ant
    check contains literal.variable match {
      case true => { //The node of question contains the split literal
        val i = node1.hasNext match {
          case false => ClauseTreeLeaf(node1) //The first (original) node which is split upon has no next literal to split and therefore the positive branch will end in a Leaf containing this node
          case true => {
            val copyNode = node1.copy
            //There is another literal to split, so this splitting is done
            ClauseTreeNode(copyNode.next,copyNode,node2)
          }
        }
        //In both cases, splitting further or not, the "not contained" branch will be empty
        (Some(i),None:Option[ClauseTree])
      }
      case false => {  //The node of question contains the split literal
        //Since both branches so far are empty, the new branches will simply be ClauseTreeLeafs with the respective nodes
        (Some(ClauseTreeLeaf(node1)),Some(ClauseTreeLeaf(node2)))
      }
    }
  }
  
  //Checks if the current split literal is contained in the node of question.
  //Either it delegates the search further downwards, or returns a ClauseTreeLeaf if an empty branch has been reached
  //For searches that were delegated further down, the branches of this ClauseTreeNode are updated according to the results of search
  def checkSubsumed(node: NodeWithIterators):(ClauseTree,SequentProofNode) = {
    if(literal.isContainedIn(node)) {
      val (resultTree,resultNode) = in.get.checkSubsumed(node)
      
      //In case the "not contained" branch is defined, it has to be searched, even tough the current literal is contained in the node of question
      //This is because a subsuming clause does not necessarily have to contain literal and could also be in the "not contained" branch
      val backNode = if (notIn.isDefined) {
        //The resulting ClauseTree of the search in the "not contained" branch is discarded
        val (_,notInNode) = notIn.get.checkSubsumed(node)
        //The resulting node is only taken if it's shorter than the one found for the "contained" branch
        if (resultNode.conclusion.size > notInNode.conclusion.size) notInNode
        else resultNode
      }
      else resultNode
      
      //The results are combined and a new ClauseTreeNode is returned
      (new ClauseTreeNode(literal,Some(resultTree),this.notIn),backNode)
    }
    else { //Splitting literal is not contained in the node of question
      if (notIn.isDefined) { //"not contained" branch is defined --> delegate the search further down
        val result = notIn.get.checkSubsumed(node)
        
        (new ClauseTreeNode(literal,this.in,Some(result._1)),result._2) //Construct new ClauseTreeNode
      }
      else { //"not contained" branch is not defined --> a new leaf node storing the node of question can be placed in this position
        val x = Some(ClauseTreeLeaf(node))
        (new ClauseTreeNode(literal,this.in,x),node.node)
      }
    }
    
  }
  override def toString: String = "[{"+literal+"}+ " + in.getOrElse("*") + " | - " + notIn.getOrElse("*") + "]"
}