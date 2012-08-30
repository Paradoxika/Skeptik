package at.logic.skeptik.proof

import collection.mutable.{HashMap => MMap, HashSet => MSet, Stack}


// ProofNode tree is rotated clockwise. That means that traversing "left" is bottom-up.
// Traversing "right" is top-down and we ensure that premises of a proof are processed before that proof.
// For convenience, children of proofs are computed as well.
class Proof[P <: ProofNode[_,P]] private(nodes: IndexedSeq[P], children: collection.Map[P,List[P]])
extends Iterable[P]
{
  // ToDo: Traversing with iterator is inefficient
  override def iterator:Iterator[P] = nodes.iterator

  override def foldRight[B](z:B)(op: (P,B) => B):B = {
    def iterate(pos:Int, acc:B): B =
      if (pos >= 0) iterate(pos-1, op(nodes(pos),acc)) else acc
    iterate(nodes.length - 1, z)
  }

  override def isEmpty:Boolean = nodes.isEmpty
  //override def head: P = nodes.head
  //override def last: P = nodes.last
  override def size:Int = nodes.length

  def root = nodes(0)
  def childrenOf(p: P) = children.getOrElse(p,Nil)

  def foldDown[X](f: (P, List[X]) => X): X = {  // TODO:  List -> Seq
    val resultFrom = MMap[P,X]()
    def iterate(pos:Int):Unit = {
      if (pos < 0) return
      val proof = nodes(pos)
      resultFrom.update(proof, f(proof, proof.premises.toList.map(resultFrom))) // TODO: remove "toList"
      iterate(pos-1)
    }
    iterate(nodes.length - 1)
    resultFrom(nodes(0))
  }

  def bottomUp[X](f:(P, List[X])=>X):Unit = {
    val resultsFromChildren = MMap[P, List[X]]()
    val lastPos = nodes.length
    def iterate(pos:Int):Unit = {
      if (pos >= lastPos) return
      val node = nodes(pos)
      val result = f(node, resultsFromChildren.getOrElse(node,Nil))
      resultsFromChildren -= node
      node.premises.foreach(premise => resultsFromChildren += (premise -> (result::resultsFromChildren.getOrElse(premise,Nil))))
      iterate(pos + 1)
    }
    iterate(0)
  }

}

object Proof {
  def apply[P <: ProofNode[_,P]](root: P) = {
    val nodes = Stack[P]()
    val children = MMap[P,List[P]]()
    val visited = MSet[P]()
    def visit(p:P):Unit = if (!visited(p)){
      visited += p
      p.premises.foreach(premise => {
        visit(premise)
        children(premise) = p::children.getOrElse(premise,Nil)
      })
      nodes.push(p)
    }
    visit(root)
    new Proof(nodes.toIndexedSeq, children)
  }
}
