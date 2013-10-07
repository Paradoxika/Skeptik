package at.logic.skeptik.algorithm.compressor.subsumption

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.expression.E

abstract class ClauseTree {
  val in: Option[ClauseTree]
  val notIn: Option[ClauseTree]
  /**
   * This method is the heart of the clauseTree structure.
   * It serves two purposes:
   * - Find an earlier inserted P-node that subsumes the input P-node.
   * - If no subsuming P-node was found, insert input P-node into the structure.
   * 
   * It does this by traversing the tree down according to the containment of the splitting literals
   * until either a leaf that can not be split further or an empty branch is found.
   */
  def checkSubsumed(node: NodeWithIterators): (ClauseTree,N)
  override def toString: String
}

/**
 * EmpyClauseTree represents the initial state of a clause tree.
 * The call for checkSubsumed simply returns a new ClauseTreeLeaf represented by input P-node.
 */
case class EmptyClauseTree() extends ClauseTree {
  val in = None:Option[ClauseTree]
  val notIn = None:Option[ClauseTree]
  def checkSubsumed(node: NodeWithIterators): (ClauseTree,N) = {
    (ClauseTreeLeaf(node),node.node)
  }
}

/**
 * A ClauseTreeLeaf represents a leaf of a clause tree.
 * 
 * There can occur two situations:
 * - The stored node is split completely according to its contained literals
 * - The stored node can be split further
 * 
 * An open issue is that if a node is stored as a leaf, 
 * its iterators will always be in their initial state, 
 * even tough some contained literals have already been checked.
 * One can not simply move the iterator whenever a splitting decision is made, 
 * since the literals don't necessarily come in the right order.
 * An attempt that I implemented that stores the literals that have already been checked before and 
 * determine the next splitting literal using this information,
 * slowed down the whole procedure a lot and was therefore discarded.
 */
case class ClauseTreeLeaf(leafNode: NodeWithIterators) extends ClauseTree {
  val in = None: Option[ClauseTree]
  val notIn = None: Option[ClauseTree]
  
  /**
   * If the stored node is split completely, 
   * then the node of question is subsumed by this node,
   * because both nodes are on the same contained/not contained path 
   * and the stored node does not contain any more literals, 
   * while the input P-node might still contain additional ones.
   * 
   * If the stored node can be split further, 
   * then a new ClauseTreeNode is created with the next literal returned by the iterators of the stored P-node
   */
  def checkSubsumed(node: NodeWithIterators): (ClauseTree,N) = {
    if (!(leafNode.hasNext) || (leafNode.node eq node.node)) { //Stored P-node is split completely
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
 * A ClauseTreeNode represents an internal node in a clause tree
 *  
 * It has two parents, representing subtrees that contain/do not contain the literal that is used to split at this CT-node.
 * A ClauseTreeNode can either be created by passing two NodeWithIterators - objects and actually performing the splitting, 
 * or simply by passing the two branches.
 */
case class ClauseTreeNode(
    literal: Literal, 
    node1: NodeWithIterators, 
    node2: NodeWithIterators, 
    inI: Option[ClauseTree] = None, 
    notInI: Option[ClauseTree] = None)
  extends ClauseTree {
  /** An alternative constructor that simply overtakes two branches
   * This constructor is used when one of the branches is being updated by calls of the checkSubsumed method
   */
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
          //The first (original) P-node which is split upon has no next literal to split 
          //and therefore the "contained" parent is a leaf containing this P-node
          case false => ClauseTreeLeaf(node1) 
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
        //Since both branches so far are empty, 
        //the new branches will simply be ClauseTreeLeafs with the respective nodes
        (Some(ClauseTreeLeaf(node1)),Some(ClauseTreeLeaf(node2)))
      }
    }
  }
  
  /**
   * Checks if the current split literal is contained in the node of question.
   * Either it delegates the search further downwards, 
   * or returns a ClauseTreeLeaf, if an empty branch has been reached.
   * For searches that were delegated further downwards, 
   * the branches of this ClauseTreeNode are updated with to the results of search.
   */
  def checkSubsumed(node: NodeWithIterators): (ClauseTree,N) = {
    if(literal.isContainedIn(node)) {
      val (resultTree,resultNode) = in.get.checkSubsumed(node)
      
      //In case the "not contained" branch is defined, 
      //it has to be searched, even tough the current literal is contained in the node of question
      //This is because a subsuming clause does not necessarily have to contain literal and 
      //could also be stored somewhere in the "not contained" branch
      val backNode = if (notIn.isDefined) {
        //The resulting clause tree of the search in the "not contained" branch is discarded
        val (_,notInNode) = notIn.get.checkSubsumed(node)
        //The resulting node is only returned if it's shorter than the one found for the "contained" branch
        if (resultNode.conclusion.size > notInNode.conclusion.size) notInNode
        else resultNode
      }
      else resultNode
      
      //The results are combined and a CL-node is returned
      (new ClauseTreeNode(literal,Some(resultTree),this.notIn),backNode)
    }
    else { //Splitting literal is not contained in the node of question
      //"not contained" branch is defined -->
      //delegate the search further downwards
      if (notIn.isDefined) { 
        val result = notIn.get.checkSubsumed(node)
        (new ClauseTreeNode(literal,this.in,Some(result._1)),result._2)
      }
      //"not contained" branch is not defined --> 
      //a new leaf node storing the input P-node can be placed in this position
      else { 
        val x = Some(ClauseTreeLeaf(node))
        (new ClauseTreeNode(literal,this.in,x),node.node)
      }
    }
    
  }
  override def toString: String = "[{"+literal+"}+ " + in.getOrElse("*") + " | - " + notIn.getOrElse("*") + "]"
}

/**
 * A structure, which stores proof nodes together with iterators over the literals occurring in the conclusion sequent.
 * 
 * This is a helper class for the clause tree structure, which is immutable. 
 * Therefore the iterators should be copied before they are moved,
 * so the original iterators hold their position in the original clause tree.
 * 
 * The class has its own hasNext and next functions, 
 * that combine the hasNext and next functions from the iterators 
 * of the antecedent and succedent of the conclusion sequent.
 */
class NodeWithIterators(val nodeI: N, sucIteratorI: Option[Iterator[E]], antIteratorI: Option[Iterator[E]]) {
  val node = nodeI
  var sucIterator = if (sucIteratorI.isDefined) sucIteratorI.get else node.conclusion.suc.iterator
  var antIterator = if (antIteratorI.isDefined) antIteratorI.get else node.conclusion.ant.iterator
  def this(node: N) = this(node,None,None)
  
  def hasNext = sucIterator.hasNext || antIterator.hasNext
  def next = if (sucIterator.hasNext) new Literal(sucIterator.next,true) else new Literal(antIterator.next,false)
  
  /**
   * The copy method returns a new object of this class with the iterators set to where they currently are
   * The iterators of the object itself are updated to duplicates of the current one and essentially stay as they are
   */
  def copy:NodeWithIterators = {
    val (itS1,itS2) = sucIterator.duplicate
    sucIterator = itS1
    val (itA1,itA2) = antIterator.duplicate
    antIterator = itA1
    new NodeWithIterators(node,Some(itS2),Some(itA2))
  }
}

/**
 * A structure that represents either a positive or negative variable.
 * This class is used in the clause tree structure.
 */
class Literal(variableI: E, posI: Boolean) {
  val variable = variableI
  val pos = posI
  //Checks weather the positive/negative variable is in the succedent/antecedent resp. of a conclusion sequent
  def isContainedIn(node: NodeWithIterators):Boolean = {
    if (pos) node.node.conclusion.suc contains variable
    else node.node.conclusion.ant contains variable
  }
  override def toString:String = (if(pos) "+" else "-")+ variable
  override def equals(obj: Any) = 
    obj.isInstanceOf[Literal] && 
    (obj.asInstanceOf[Literal].pos == this.pos) && 
    (obj.asInstanceOf[Literal].variable eq this.variable)
}