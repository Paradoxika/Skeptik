package at.logic.skeptik.proof

import collection.mutable.{HashMap => MMap, HashSet => MSet, Stack}


// TODO: ProofNodeCollection is not really conforming to the standards of 
// Scala's collection framework.
// Eventually, we should rethink and improve it.


// Proof tree is rotated clockwise. That means that traversing "left" is bottom-up.
// Traversing "right" is top-down and we ensure that premises of a proof are processed before that proof.
// For convenience, children of proofs are computed as well.
class ProofNodeCollection[P <: Proof[_,P]] private(nodeArray: Seq[P], children: collection.Map[P,List[P]])
extends Iterable[P]
{
  override def iterator:Iterator[P] = new SimpleIterator(nodeArray)

  // Some optimisations (more TODO)
  override def foldRight[B](z:B)(op: (P,B) => B):B = {
    def iterate(pos:Int, acc:B): B =
      if (pos >= 0) iterate(pos-1, op(nodeArray(pos),acc)) else acc
    iterate(nodeArray.length - 1, z)
  }

  override def isEmpty:Boolean = nodeArray.isEmpty
  override def head: P = nodeArray(0)
  override def last: P = nodeArray(nodeArray.length - 1)
  override def size:Int = nodeArray.length
  // Array is not variant...
  // override def toArray[B >: P]:Array[B] = nodeArray.clone()

  def root = nodeArray(0)
  def childrenOf(p: P) = children.getOrElse(p,Nil)

  def foldDown[X](f: (P, List[X]) => X): X = {  // TODO:  List -> Seq
    val resultFrom = MMap[P,X]()
    def iterate(pos:Int):Unit = {
      if (pos < 0) return
      val proof = nodeArray(pos)
      resultFrom.update(proof, f(proof, proof.premises.toList.map(resultFrom))) // TODO: remove "toList"
      iterate(pos-1)
    }
    iterate(nodeArray.length - 1)
    resultFrom(nodeArray(0))
  }

  // a top down foreach
  def foreachDown[U](f: (P) => U):Unit = {
    def iterate(pos: Int):Unit = if (pos >= 0) {
      f(nodeArray(pos))
      iterate(pos - 1)
    }
    iterate(nodeArray.length - 1)
  }

  def bottomUp[X](f:(P, List[X])=>X):Unit = {
    val resultsFromChildren : MMap[P, List[X]] = MMap()
    val lastPos = nodeArray.length
    def iterate(pos:Int):Unit = {
      if (pos >= lastPos) return
      val node = nodeArray(pos)
      val result = f(node, resultsFromChildren.getOrElse(node,Nil))
      resultsFromChildren -= node
      node.premises.foreach(premise => {
          resultsFromChildren +=
            (premise -> (result::resultsFromChildren.getOrElse(premise,Nil)))
      })
      iterate(pos + 1)
    }
    iterate(0)
  }

  private class SimpleIterator (nodeArray: Seq[P])
  extends BufferedIterator[P] {
    var pos = 0

    def next() = {
      if (!hasNext) throw new Exception("Iterator terminated");
      val ret = nodeArray(pos)
      pos += 1
      ret
    }

    def head = nodeArray(pos)
    def hasNext = pos < nodeArray.length
  }
}

object ProofNodeCollection {
  def apply[P <: Proof[_,P]](root: P) = {
    val nodes = Stack[P]()
    val children = MMap[P,List[P]]()
    val visited = MSet[P]()
    def visit(p:P):Unit = if (!visited(p)){
      visited += p
      p.premises.foreach(premise => {
        visit(premise)
        children.update(premise, p::children.getOrElse(premise,Nil))
      })
      nodes.push(p)
    }
    visit(root)
    new ProofNodeCollection(nodes, children)
  }
}
