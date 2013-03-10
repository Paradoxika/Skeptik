package at.logic.skeptik.proof

import collection.mutable.{HashMap => MMap, HashSet => MSet, Stack}
import annotation.tailrec

// ProofNode tree is rotated clockwise. That means that traversing "left" is bottom-up.
// Traversing "right" is top-down and we ensure that premises of a proof are processed before that proof.
// ToDo: The underscore type parameter seems to be causing problems.
class Proof[P <: ProofNode[_,P]] private(nodes: IndexedSeq[P], val childrenOf: collection.Map[P,Seq[P]])
extends Iterable[P]
{
  override def iterator:Iterator[P] = nodes.iterator
  override def isEmpty:Boolean = nodes.isEmpty
  override val size:Int = nodes.length // ToDo: nodes is IndexedSeq, and nodes.length should take constant time. Therefore it might be ok to make this a def instead of a val

  def root = nodes(0)


  def foldDown[X](f: (P, Seq[X]) => X): X = {
    val resultFrom = MMap[P,X]()
    @tailrec def iterate(pos:Int):Unit = {
      if (pos < 0) return
      val node = nodes(pos)
      resultFrom(node) = f(node, node.premises.map(resultFrom)) // TODO: remove "toList"
      iterate(pos-1)
    }
    iterate(nodes.length - 1)
    resultFrom(nodes(0))
  }

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

  override def toString = {
    var counter = 0; var result = "";
    def visitNode(n:P, r:Seq[Int]): Int = {
      counter += 1
      result += counter.toString + ": {" + n.conclusion + "} \t:" +
                n.name + "(" + r.mkString(", ") + ")[" + n.parameters.mkString(", ") + "]\n"
      counter
    }
    foldDown(visitNode)
    result
  }
  
}

object Proof {
  def apply[P <: ProofNode[_,P]](root: P) = {
    val nodes = Stack[P]()
    val children = MMap[P,Seq[P]](root -> Seq())
    val visited = MSet[P]()
    def visit(p:P):Unit = if (!visited(p)){
      visited += p
      p.premises.foreach(premise => {
        visit(premise)
        children(premise) = p +: children.getOrElse(premise,Seq())
      })
      nodes.push(p)
    }
    visit(root)
    new Proof(nodes.toIndexedSeq, children)
  }
}