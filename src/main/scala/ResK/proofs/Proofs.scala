package ResK.proofs

import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, Stack}
import ResK.judgments.Judgment
import ResK.utilities.prettyPrinting._

abstract class Proof[+J <: Judgment, +P <: Proof[J,P] : ClassManifest] (val name: String, val premises: List[P])
{
  private val self = asInstanceOf[P]
  def conclusion : J
  def parameters: List[Any] = Nil
  override def toString = {
    var counter = 0; var result = "";
    def visitNode(n:P, r:List[Int]): Int = {
      counter += 1
      result += counter.toString + ": {" + n.conclusion + "} \t:" +
                n.name + "(" + listToCSVString(r) + ")[" + listToCSVString(parameters) + "]\n"
      counter
    }
    ProofNodeCollection(self).foldDown(visitNode)
    result
  }
}


// Proof tree is rotated clockwise. That means that traversing "left" is bottom-up.
// Traversing "right" is top-down and we ensure that premises of a proof are processed before that proof.
// For convenience, children of proofs are computed as well.
class ProofNodeCollection[P <: Proof[_,P]] private(nodeArray: Array[P], children: scala.collection.Map[P,List[P]])
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
  def childrenOf = children

  def foldDown[X](f: (P, List[X]) => X): X = {
    val resultFrom = MMap[P,X]()
    def iterate(pos:Int):Unit = {
      if (pos < 0) return
      val proof = nodeArray(pos)
      resultFrom.update(proof, f(proof, proof.premises.map(resultFrom)))
      iterate(pos-1)
    }
    iterate(nodeArray.length - 1)
    resultFrom(nodeArray(0))
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

  private class SimpleIterator (nodeArray: Array[P])
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
  def apply[P <: Proof[_,P] : ClassManifest](root: P) = {
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
    new ProofNodeCollection(nodes.toArray, children)
  }
}
