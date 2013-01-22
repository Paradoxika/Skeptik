package at.logic.skeptik

import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof.oldResolution.defs._
import at.logic.skeptik.proof.oldResolution.typeAliases._

import collection.mutable.{HashMap => MMap, HashSet => MSet}


// ToDo: all these functions should be moved outside the util package.
// the util package should not depend on other packages in Skeptik.


// A collection of functions to analyse proofs and differences between proofs.
object help {

  def proofToMap(proof: Proof[SequentProofNode]) =
    proof.foldLeft(Map[Sequent,List[Sequent]]()) { (map,node) => node match {
      case CutIC(left,right,_,_) => map + (node.conclusion -> ((left.conclusion)::((right.conclusion)::(map.getOrElse(node.conclusion,Nil)))))
      case _ => map
    }
  }
  
  // proof must be DAGified
  def proofToSequentMap(proof: Proof[SequentProofNode]) =
    proof.foldLeft(Map[Sequent, (Sequent,Sequent)]()) { (map,node) =>
      node match {
        case CutIC(left,right,_,_) => map + (node.conclusion -> (left.conclusion, right.conclusion))
        case _ => map
      }
    }

  def diffMap[A,B,C](ma: Map[A,B], mb: Map[A,C]) = {
    val keys = (ma.keySet) union (mb.keySet)
   
    keys.foldLeft((Map[A,B](),Map[A,C]())) { case ((da,db),k) =>
      (ma contains k, mb contains k) match {
        case (true,true) if (ma(k) != mb(k)) => (da + (k -> ma(k)), db + (k -> mb(k)))
        case (true,false) => (da + (k -> ma(k)), db)
        case (false,true) => (da, db + (k -> mb(k)))
        case _ => (da, db)
      }
    }
  }

  object simplifySequent {
    val map = MMap[E,E]()
    private var next = 0
    def trans(exp: E) = if (map.contains(exp)) map(exp) else { map += (exp -> Var("#" + next,o)) ; next += 1 ; map(exp) }
    def apply(seq: Sequent) = new Sequent(seq.ant.map(trans _), seq.suc.map(trans _))
  }

  def convertToSequent(clause: Clause) = {
    var ant: List[E] = Nil
    var suc: List[E] = Nil
    clause.foreach { l => if (l.polarity) ant = Var(l.atom.toString,o)::ant else suc = Var(l.atom.toString,o)::suc }
    new Sequent(ant, suc)
  }

  def convertToSequentProofNode(p: proof.oldResolution.ProofNode) = {
    val toSequent = collection.mutable.HashMap[proof.oldResolution.ProofNode,SequentProofNode]()
    def recursive(p: proof.oldResolution.ProofNode):SequentProofNode = if (toSequent contains p) toSequent(p) else {
      val seq = p match {
        case proof.oldResolution.Resolvent(left,right) => CutIC(recursive(left), recursive(right))
        case proof.oldResolution.Input(clause) => Axiom(convertToSequent(clause))
      }
      toSequent.update(p, seq)
      seq
    }
    recursive(p)
  }

  def printDigraph[A](filename: String, in: Map[A,List[A]]) = {
    val out = new java.io.PrintStream(filename)
    var next = 0
    val map = collection.mutable.HashMap[A,String]()
    def nodeString(node: A) =
      if (map contains node) map(node) else {
        val ret = "n" + next
        map.update(node, ret)
        next = next + 1
        ret
      }
    out.println("digraph proof {")
    for (k <- in.keys ; v <- in(k)) {
      out.println("  " + nodeString(k) + " -> " + nodeString(v) + ";")
    }
    map.foreach { t => out.println("  " + t._2 + " [label=\"" + t._1 + "\"];") }
    out.println("}")
    out.close()
  }

  def makeMapOfChildren(node: SequentProofNode, nodeCollection: Proof[SequentProofNode]) = {
    class Wrap(val n: SequentProofNode) {
      override def equals(other: Any):Boolean = other match {
        case w:Wrap => w.n eq n
        case _ => false
      }
      override def hashCode = n.hashCode
      override def toString = n match {
        case CutIC(_,_,pivot,_) => pivot.toString
        case _ => "Axiom"
      }
    }

    val map = MMap[Wrap,List[Wrap]]()
    val visited = MSet[SequentProofNode]()
    def addChildrenOf(parent: SequentProofNode):Unit = {
      if (visited contains parent) return else visited += parent
      for (child <- nodeCollection.childrenOf(parent)) {
        map.update(new Wrap(child), new Wrap(parent)::(map.getOrElse(new Wrap(child),Nil)))
        addChildrenOf(child)
      }
      for (premise <- parent.premises)
        if (!(map contains new Wrap(premise))) map.update(new Wrap(parent), new Wrap(premise)::(map.getOrElse(new Wrap(parent),Nil)))
    }
    addChildrenOf(node)
    map.toMap
  }

}
