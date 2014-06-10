package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap}

abstract class CongruenceGraph(val lazyEdges: Map[(E,E),Option[EqW]]) {
  
  def newGraph(edges: Map[(E,E),Option[EqW]]): CongruenceGraph
  
  def lazyAddEdge(u: E, v: E, eq: Option[EqW]): CongruenceGraph = eq match {
    case Some(_) => {
      if (lazyEdges.isDefinedAt((u,v)) || lazyEdges.isDefinedAt((v,u))){
        val in = lazyEdges.getOrElse((u,v),lazyEdges.get((v,u)))
        if (!in.isDefined) {
          println("replacing bad vs good")
        }
      }
      newGraph(lazyEdges - ((u,v)) - ((v,u)) + ((u,v) -> eq))
    }
    case None => if (lazyEdges.isDefinedAt((u,v)) || lazyEdges.isDefinedAt((v,u))) this else newGraph(lazyEdges +((u,v) -> eq))
  }
  
  def addEdge(u: E, v: E, eq: Option[EqW]): CongruenceGraph
  
  def explain(u: E, v: E)(implicit eqReferences: MMap[(E,E),EqW]): Option[EquationPath] 
  
  def subterms(term: E): Seq[E] = term match {
    case App(u,v) => {
      val x = uncurriedTerms(u) ++ uncurriedTerms(v)
//      println("subterms of " + term + " uncurried of " + u + " ~> " + uncurriedTerms(u) + " and of v: " + uncurriedTerms(v))
      x
    }
    case _ => {
//      println(term + " is such a term")
      Seq()
    }
  }
  
  def uncurriedTerms(term: E): Seq[E] = term.t match {
    case Arrow(_,_) => {
      term match {
        case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
        case _ => Seq()
      }
    }
    case _ => {
//      println("non constant good subterm: " + term)
      Seq(term)
    }
  }
  
  def buildDD(t1: E, eq: Option[EqW], t2: E)(implicit eqReferences: MMap[(E,E),EqW]) = eq match {
    case None => {
      val (sub1,sub2) = (subterms(t1),subterms(t2))
      
//      println((sub1,sub2) + " subterms of " + (t1,t2))
//      println((subterms(t1).mkString(";"),subterms(t2).mkString(";")) + " subterms of " + (t1,t2))
      if (sub1.size != sub2.size) println("subterms don't match for " + (t1,t2) + " t: " + (t1.t,t2.t) + " s: " + (sub1,sub2) + "\n" + this)
      require(sub1.size == sub2.size)
      val explOpts = (sub1 zip sub2).map(tuple => {
        
        val x = explain(tuple._1,tuple._2)
//        println("while building dd, explaining: " + (tuple) + " result: " + x)
        x
      })
      val x = explOpts.filter(_.isDefined).map(_.get).toSet
//      println((t1,t2) +" produces expls: " + x)
//      if (x.isEmpty) println("empty ddTrees for " + (t1,t2))
//      if (t1.toString == "(f2 c_3 c_5)" && t2.toString() == "(f2 (f2 c_3 c_3) c_5)") println("found it!; result: " + x + "graph:\n"+this)
      x
    }
    case Some(e) => {
//        println("skipping deduce trees! for " + e)
      Set[EquationPath]()
    }
  }
}