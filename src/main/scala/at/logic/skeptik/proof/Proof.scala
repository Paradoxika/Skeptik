package at.logic.skeptik.proof

import language.implicitConversions

import collection.mutable.{HashMap => MMap, HashSet => MSet, Stack}
import annotation.tailrec

import at.logic.skeptik.judgment.Judgment

// ProofNode tree is rotated clockwise. That means that traversing "left" is bottom-up.
// Traversing "right" is top-down and we ensure that premises of a proof are processed before that proof.
class Proof[P <: ProofNode[Judgment,P]](val root: P, val leftRight: Boolean = true, val permutation: IndexedSeq[P] = IndexedSeq[P]())
extends Iterable[P]
{ 
  
  def this(root: P, permutation: IndexedSeq[P]) = this(root,true, permutation)
  def initialize() = {
    val nodes = Stack[P]()
    val children = MMap[P,IndexedSeq[P]](root -> IndexedSeq())
    val visited = MSet[P]()
    var counter = 0
    def visit(p:P):Unit = if (!visited(p)){
      visited += p
      val pr = if (leftRight) p.premises else p.premises.reverse
      pr.foreach(premise => {
        if (permutation.isEmpty) {
          visit(premise)
        }
        children(premise) = p +: children.getOrElse(premise,IndexedSeq())
      })
      if (!permutation.isEmpty && (counter + 1) < permutation.size) {
        counter = counter + 1
        visit(permutation(counter))
      }
      nodes.push(p)
    }
    visit(root)
    (nodes.toIndexedSeq, children.toMap)
  }
  
  val (nodes, childrenOf) = initialize()
    
  override def iterator:Iterator[P] = nodes.iterator
  override def isEmpty:Boolean = nodes.isEmpty
  override lazy val size:Int = nodes.length


  /**
    * The method foldDown consumes the proof in a topDown traversal (i.e. from the leaves
    * to the root). It applyies the function taken as parameter to each node.
    * In the case of the leaves of the proof, the second parameter of f will be Nil
    *
    * @param f  The function f takes the current node visited and a sequence of the results of the
    *           recursive calls of f in the parents of the current node (a node is the child of its
    *           premises)
    * @tparam X The type of the result generated after consuming the proof
    * @return   The recursive consumption of the proof applying the function f
    */
  def foldDown[X](f: (P, Seq[X]) => X): X = {
    val resultFrom = MMap[P,X]()
    @tailrec def iterate(pos:Int):Unit = {
      if (pos < 0) return
      val node = nodes(pos)
      resultFrom(node) = f(node, node.premises.map(resultFrom))
      iterate(pos-1)
    }
    iterate(nodes.length - 1)
    resultFrom(nodes(0))
  }
  
  def foldDown2[X](f: (P, Seq[X]) => X,permutation: Seq[Int]): X = {
    val resultFrom = MMap[P,X]()
    @tailrec def iterate(pos:Int):Unit = {
      if (pos < 0) return
      val node = nodes(permutation(pos))
//      println("foldDown visits " + node + " at pos: " + pos + " permutation at pos: " + permutation(pos))
      resultFrom(node) = f(node, node.premises.map(resultFrom))
      iterate(pos-1)
    }
    iterate(nodes.length - 1)
    resultFrom(nodes(permutation(0)))
  }

  /**
    * The method bottomUp traverse the proof in a bottomUp traversal (i.e. from the
    * root to the leaves). It applyies the function taken as parameter to each node.
    * In the case of the root of the proof, the second parameter of f will be Nil
    *
    * @param f  The function f takes the current node visited and a sequence of the results of the
    *           recursive calls of f in the children of the current node (a node is the child of its
    *           premises)
    * @tparam X The type of the result generated after consuming the proof
    */
  def bottomUp[X](f:(P, Seq[X])=>X):Unit = {
    val resultsFromChildren = MMap[P, Seq[X]]()
    @tailrec def iterate(pos:Int):Unit = {
      if (pos >= size) return
      val node = nodes(pos)
      val result = f(node, resultsFromChildren.getOrElse(node,Nil))
      resultsFromChildren -= node
      node.premises.foreach(premise => resultsFromChildren(premise) = (result +: resultsFromChildren.getOrElse(premise, Seq())))
      iterate(pos + 1)
    }
    iterate(0)
  }
  
  def bottomUp2[X](f:(P, Seq[X])=>X, permutation: Seq[Int]):Unit = {
    val resultsFromChildren = MMap[P, Seq[X]]()
    @tailrec def iterate(pos:Int):Unit = {
      if (pos >= size) return
      val node = nodes(permutation(pos))
      val result = f(node, resultsFromChildren.getOrElse(node,Nil))
      resultsFromChildren -= node
      node.premises.foreach(premise => resultsFromChildren(premise) = (result +: resultsFromChildren.getOrElse(premise, Seq())))
      iterate(pos + 1)
    }
    iterate(0)
  }

  /**
    * The method topDown traverse the proof in a topDown traversal (i.e. from the
    * leaves to the root). It applyies the function taken as parameter to each node.
    * In the case of the leaves of the proof, the second parameter of f will be Nil
    *
    * @param f  The function f takes the current node visited and a sequence of the results of the
    *           recursive calls of f in the parents of the current node (a node is the child of its
    *           premises)
    * @tparam X The type of the result generated after consuming the proof
    */
  def topDown[X](f: (P, Seq[X]) => X): Unit = {
    val resultsFromParents = MMap[P, Seq[X]]()
    @tailrec def iterate(pos: Int): Unit = {
      if (pos < 0) return
      val node = nodes(pos)
      val result = f(node, resultsFromParents.getOrElse(node, Nil))
      resultsFromParents -= node
      node.premises.foreach(premise => resultsFromParents(premise) = (result +: resultsFromParents.getOrElse(premise, Seq())))
      iterate(pos - 1)
    }
    iterate(nodes.length - 1)
  }

  override def toString = {
    var counter = 0; var result = "";
    foldDown { (n:P, r:Seq[Int]) =>
      counter += 1
      result += counter.toString + ": {" + n.conclusion + "} \t: " +
                n.name + "(" + r.mkString(", ") + ")[" + n.parameters.mkString(", ") + "]\n"
      counter
    }
    result
  }
  
}

object Proof {
  implicit def apply[P <: ProofNode[Judgment,P]](root: P) = new Proof(root)
}