package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.congruence._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

object proofTreeTest {
  def main(args : Array[String]) : Unit = {
    var tree = new ProofForest
    
    val t = o
    
    val a = new Var("a",t)
    val a1 = new Var("a1",t)
    val a2 = new Var("a2",t)
    val a3 = new Var("a3",t)
    val b = new Var("b",t)
    val b1 = new Var("b1",t)
    val b2 = new Var("b2",t)
    val b3 = new Var("b3",t)
    val c = new Var("c",t)
    val c1 = new Var("c1",t)
    val c2 = new Var("c2",t)
    val c3 = new Var("c3",t)
    val d = new Var("d",t)
    val e = new Var("e",t)
    
    val f = new Var("f",Arrow(t,t))
    
    val t1 = App(f,a)
    val t2 = App(f,b)
    
    val eqReferences = MMap[(E,E),EqW]()
    
    tree = tree.addEdge(a, b, Some(EqW(a,b,eqReferences)))
    tree = tree.addEdge(b, c, Some(EqW(b,c,eqReferences)))
    println("1 "+tree.printNode(a))
    println(tree.next)
//    tree = tree.reverseToRoot(b)
//    println("2 "+tree.printNode(c))
    
    tree = tree.addEdge(d, e, Some(EqW(d,e,eqReferences)))
    
    tree = tree.addEdge(b, d, Some(EqW(b,d,eqReferences)))
    
    println(tree.printNode(e))
    println(tree.printNode(c))
    println(tree.rootSize(b))
    
    tree = tree.addEdge(b1,d,Some(EqW(b1,d,eqReferences)))
    tree = tree.addEdge(b2,t2,Some(EqW(b2,t2,eqReferences)))
    tree = tree.addEdge(t1, t2, None)
    tree = tree.addEdge(t1, b1, Some(EqW(b1,t1,eqReferences)))
    
    println(tree.next)
    
    println(tree.printNode(a))
    
    tree = tree.addEdge(c1, c2, Some(EqW(c1,c2,eqReferences)))
    
    println(tree.ncaPath(e,c1))
    
    println(tree.ncaPath(e,b))
    
    println(tree.explain(e,b2))
    
  }
}