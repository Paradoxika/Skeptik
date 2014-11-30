package at.logic.skeptik.congruence

import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._

object SubtermTest {
  def main(args: Array[String]) = {
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
    
    val f1 = new Var("f",Arrow(t,Arrow(t,t)))
    
    val h = new Var("h",Arrow(t,Arrow(t,Arrow(t,t))))
    
    val op = new Var("op",Arrow(t,Arrow(t,t)))
    
    val t1 = App(App(App(h,a),b),c)
    
    val t2 = App(App(App(h,c1),c2),c3)
    
    val x1 = App(f1,a)
    val x2 = App(f1,b)
    val y1 = App(x1,b)
    val y2 = App(x2,a)
    val z1 = App(op,y1)
    val z2 = App(op,y2)
    val v1 = App(z1,a)
    val v2 = App(z2,a)
    println(v1)
    println(subterms(v1))
    
    val s1 = subterms(t1)
    val s2 = subterms(t2)
    
    (s1 zip s2).foreach(println)
  }
  
  def subterms(term: E): Seq[E] = term match {
    case App(u,v) => {
      println(uncurriedTerms(u) +"~"+ uncurriedTerms(v))
      uncurriedTerms(u) ++ uncurriedTerms(v)
    }
    case _ => Seq()
  }
  
  def uncurriedTerms(term: E): Seq[E] = term.t match {
    case Arrow(_,_) => {
      term match {
        case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
        case _ => Seq()
      }
    }
    case _ => Seq(term)
  }
}