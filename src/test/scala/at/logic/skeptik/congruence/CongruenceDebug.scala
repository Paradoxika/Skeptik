package at.logic.skeptik.congruence

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.congruence._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.proof._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import at.logic.skeptik.algorithm.compressor.congruence._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.lk.R

object CongruenceDebug {
  def main(args: Array[String]):Unit = {
//    val proof = ProofParserVeriT.read("F:/Proofs/QF_UF/QG-classification/qg6/iso_icl_sk004.smt2")
//    CongruenceTest(proof)
    val testcase = -2
    
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
    
    val x = new Var("x",Arrow(t,t))
    
    val op = new Var("op",Arrow(t,Arrow(t,t)))
    val e4 = new Var("e4",t)
    val skc1 = new Var("skc1",t)
    val e3 = new Var("e3",t)
    val e1 = new Var("e1",t)
    
    def origSubterms(term: E): Seq[E] = (term,term.t) match {
      case (App(u,v),Arrow(_,_)) => origSubterms(v) ++ origSubterms(u)
      case (_, Arrow(_,_)) => Seq()
      case (t, _) => Seq(term)
    }
    
//    println(App(x,b).t)
//    
//    val z1 = App(f,App(x,b))
//    val z2 = App(f,App(x,c))
//    
//    println(z1 + " type: " + z1.t)
//    println(z2 + " type: " + z2.t+"\n")
    
//    Eq(App(f,a),App(f,a))
    
    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val reflMap = MMap[E,N]()
    
//    val set = Set(EqW(a,b),EqW(b,a))
    
//    println("set: " + set)
    
//    var con: AbstractCongruence = FibonacciCongruence(eqReferences)
    var con2: AbstractCongruence = new ProofTreeCongruence()
    var con: AbstractCongruence = FibConNew(eqReferences)
//    var con: AbstractCongruence = ProofTreeConNew(eqReferences)
    
    testcase match {
      
      case -8 => {
        val t1 = App(App(f1,a),e);
        val t2 = App(App(f1,d),e);
        con = con.addEquality(EqW(c1,t1));
        con = con.addEquality(EqW(a,c));
        con = con.addEquality(EqW(b,c));
//        con = con.addEquality(EqW(a1,d));
//        con = con.addEquality(EqW(a2,d));
//        con = con.addEquality(EqW(a3,d));
        con = con.addEquality(EqW(c,d));
        con = con.addEquality(EqW(c2,t2));
//        con = con.addEquality(EqW(e,b));
        con = con.updateLazy
//        con = con.addEquality(EqW(c2,c1));
        val path = con.explain(c1, c2)
        println(con.g)
        println(path)
      }
      
      case -7 => {
        con = con.addEquality(EqW(a,b)).updateLazy
        val path = con.explain(a, b)
        println(con.g)
        println(path)
      }
      
      case -6 => {
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,t1),b)
        con = con.addEquality(EqW(a,t1)).addNode(t2)
        con = con.updateLazy
        val path = con.explain(t1, t2)
        println(path)
        val proof = path.get.toProof.get
        
        println(proof)
        println(measure(proof))
        
      }
      
      case -5 => {
        con = con.addEquality(EqW(a,b)).addEquality(EqW(b,c)).addEquality(EqW(c,e)).addEquality(EqW(e,d))
        con = con.updateLazy
        val path = con.explain(a, d).get
        println(con.g)
        println(path)
        
        val proof = path.toProof.get
        
        println(proof)
        println(measure(proof))
        
      }
      
      case -4 => {
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,b),a)
        con = con.addEquality(EqW(a,c)).addEquality(EqW(b,c)).addNode(t1).addNode(t2)
        con = con.updateLazy
        println(eqReferences)
        val path = con.explain(t1,t2)
        
        println(path)
        println(path.get.toProof)
      }
      
      case -3 => {
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,b),a)
        con = con.addEquality(EqW(a,b,false)).addEquality(EqW(b,a,false)).addNode(t1).addNode(t2)
        con = con.updateLazy
        println(eqReferences)
        val path = con.explain(t1,t2)
        
        println(path)
        println(path.get.toProof)
        
        con2 = con2.addEquality(EqW(a,b,false)).addEquality(EqW(b,a,false)).addNode(t1).addNode(t2)
        val path2 = con2.explain(t1,t2)
        val proof = path2.get.toProof.get
        println(path2)
        println(proof)
        println(ProofTreeCNewNew(proof))
      }
      
      case -2 => {
        val x1 = App(f1,a)
        val x2 = App(f1,b)
        val y1 = App(x1,b)
        val y2 = App(x2,a)
        val z1 = App(op,y1)
        val z2 = App(op,y2)
        val v1 = App(z1,a)
        val v2 = App(z2,a)
        val eq1 = EqW(a,b)
        println((v1,v2))
        con = con.addEquality(eq1).addNode(v1).addNode(v2)
        con = con.updateLazy
        println("congruent?" + con.isCongruent(v1, v2))
        val path = con.explain(v1, v2).get
        println(path.toString(true))
        val proof = path.toProof.get
        println(proof)
        val resnode = Axiom(new Sequent(Seq(),Seq(eq1.equality)))
        val newProof = Proof(R(proof.root,resnode).asInstanceOf[N])
        println(newProof)
        FibonacciCNew(newProof)
        println(origSubterms(v1))
      }
      
      case -1 => {
        val s1 = App(f1,a)
        val s2 = App(f1,c)
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,c),d)
        val eq1 = EqW(a,e)
        val eq2 = EqW(b,d)
        val eq3 = EqW(c,e)
        println(t1 + ": " + t1.t + " and " + t2 + " : " + t2.t)
        con = con.addEquality(eq1).addEquality(eq2).addEquality(eq3).addNode(t1).addNode(t2)
        con = con.updateLazy
//        con = con.addEquality(eq1).addEquality(eq2)
        println(con.g)
//        
        val path = con.explain(t1, t2).get
//        
        val proof = path.toProof.get
//      
        println(path)
        
        println(proof)
//        
        println(path.pred.get.label)
//        
        proof.root.conclusion.suc.foreach(e => println(e.t))
      }
      
      case 0 => {
        //a = b; b = c; f(a) = d; f(c) = e; 
        
        val t1 = new App(f,a)
        val t2 = new App(f,c)
        
        val eq1 = EqW(a,b)
        val eq2 = EqW(b,c)
        
        val eq3 = EqW(t1,d)
        val eq4 = EqW(t2,e)
        
        println("Input: " + List(eq1,eq2,eq3,eq4).mkString(","))
        
        con = con.addEquality(eq1)
        con = con.addEquality(eq2)
        con = con.addEquality(eq3)
        con = con.addEquality(eq4)
        
//        con = con.resolveDeducedQueue
        
        
        println(con.g)
        val path = con.explain(e,d).getOrElse(EquationPath(e,None))
    //    println(t1 + " = " + t2 + " because: " + con.explain(t1, t2).collectLabels)
        println(path)
        println(e + " = " + d + " because: " + path.originalEqs)
        
        println("\n"+path.toProof.get)
//        println("trans chain?: " + con.pathTreetoProof(path))
      }
      case 1 => {
        
        //a = b1, b1 = b2, b2 = b3, b3 = c, f(a1)=a, f(c1) = c, a1 = c1
//        val t1 = App(App(f,a1),a1)
//        val t2 = App(App(f,c1),c1)
        
        val t1 = App(f,a1)
        val t2 = App(f,c1)
        
        con = con.addEquality(EqW(a,b1))
        con = con.addEquality(EqW(b1,b2))
        con = con.addEquality(EqW(b2,b3))
        con = con.addEquality(EqW(b3,c))
        con = con.addEquality(EqW(t1,a))
        con = con.addEquality(EqW(t2,c))
        con = con.addEquality(EqW(a1,c1))
        
//        con.resolveDeduced

        println(con.g)
        
        val path = con.explain(a,c).getOrElse(EquationPath(a,None))
        println(a + " = " + c + " because: " + path.originalEqs)
        
//        con = con.resolveDeduced(t1, t2)
        val path2 = con.explain(a,c).getOrElse(EquationPath(a,None))
        println(a + " = " + c + " because: " + path2.originalEqs)
        
        println("\n"+path.toProof.get)
      }
      case 2 => {
        //a1 = b1, a1 = c1, f(a1) = a, f(b1) = b, f(c1) = c
        val t1 = App(f,a1)
        val t2 = App(f,b1)
        val t3 = App(f,c1)
        
        con = con.addEquality(EqW(a1,b1))
        con = con.addEquality(EqW(a1,c1))
        con = con.addEquality(EqW(t1,a))
        con = con.addEquality(EqW(t2,b))
        con = con.addEquality(EqW(t3,c))
        
//        con.resolveDeduced
        
        val path = con.explain(a,c).getOrElse(EquationPath(a,None))
        println(con.g)
        println(a + " = " + c + " because: " + path.originalEqs)
        
        println("\n"+path.toProof.get)
      }
      
      case 3 => {
        //g(l,h) = d, c = d, g(l,d) = a, e = c, e = b, b = h
        
        val g = new Var("g",Arrow(t,Arrow(t,t)))
        val l = new Var("l",t)
//        val i = new Var("i",Arrow(i,i))
        val h = new Var("h",t)
        
        val t1 = App(App(g,l),h)
        val t2 = App(App(g,l),d)
        
        val eqs = List(EqW(t1,d),EqW(t2,a),EqW(c,d),EqW(e,c),EqW(e,b),EqW(b1,b),EqW(b1,h))
        println("===Input: " + eqs.mkString(","))
        con = con.addAll(eqs).updateLazy
//        con = con.addEquality(EqW(t1,d,eqReferences))
//        con = con.addEquality(EqW(c,d,eqReferences))
//        con = con.addEquality(EqW(t2,a,eqReferences))
//        con = con.addEquality(EqW(e,c,eqReferences))
//        con = con.addEquality(EqW(e,b,eqReferences))
//        con = con.addEquality(EqW(b1,b,eqReferences))
//        con = con.addEquality(EqW(b1,h,eqReferences))
        
//        con = con.addEquality(EqW(d,h,eqReferences))
        
//        con = con.resolveDeducedQueue
        
        
        
//        con = con.resolveDeducedQueue
        
        val path = con.explain(a,b).getOrElse(EquationPath(a,None))
        println(con.g)
        println(a + " = " + b + " because: " + path.originalEqs)

        val eqs2 = List(EqW(d,c1),EqW(c1,c2),EqW(c2,c3),EqW(c3,h))
        println("\n\n\n===Input: " + (eqs ++ eqs2).mkString(","))
        con = eqs2.foldLeft(con)({(A,B) => A.addEquality(B)})
        con = con.updateLazy
//        con = con.addEquality(Eq(d,c1))
////        con = con.addEquality(Eq(c1,c2))
//        con = con.addEquality(Eq(c1,c2))
//        con = con.addEquality(Eq(c2,c3))
//        con = con.addEquality(Eq(c3,h))

        val path2 = con.explain(a, b).getOrElse(EquationPath(a,None))
        println(con.g)
        println(a + " = " + b + " because: " + path2.originalEqs)
        
//        println("trans chain?: " + path2.toProof)
        
        
        println("\n"+path.toProof.get)
        
        println("\n"+path2.toProof.get)
      }
      case 4 => {
        //(op e4 e3),(op e3 e3) from
        //((op (op e4 skc1) (op skc1 e4)) = (op e3 e3)), ((op (op e4 skc1)) = (op e3)), (e4 = (op e4 e3)), (e3 = (op e1 e4)), (e4 = (op (op e4 skc1) (op skc1 e4))), ((op e1 e4) = (op skc1 e4)))
        //((op (op e4 skc1)) = (op e3)), (e4 = (op e4 e3)), ((op (op e3 skc1) (op skc1 e3)) = e3), (e3 = (op e1 e4)), ((op (op e3 skc1) (op skc1 e3)) = (op e4 skc1)), (e4 = (op (op e4 skc1) (op skc1 e4))), ((op e1 e4) = (op skc1 e4))
        
        
        //((op e1 e3) = e1), (e4 = (op e4 e3)), ((op (op e3 skc1) (op skc1 e3)) = e3), (e1 = skc1), (e3 = (op e1 e4)), (e4 = (op e3 e1)), ((op e1 e3) = (op skc1 e3)), (e4 = (op (op e4 skc1) (op skc1 e4))), ((op e1 e4) = (op skc1 e4))
        
        val subt1 = App(App(op,e4),skc1) // (op e4 skc1)
        val subt2 = App(App(op,skc1),e4) // (op skc1 e4)
        val t1 = App(App(op,subt1),subt2) //(op (op e4 skc1) (op skc1 e4))
        val t2 = App(App(op,e3),e3) // (op e3 e3)
        val t3 = App(op,subt1) //(op (op e4 skc1))
        val t4 = App(op,e3) //(op e3)
        val t5 = App(App(op,e1),e4) //(op e1 e4)
        val t6 = App(App(op,e4),e3) //(op e4 e3)
        val t7 = App(App(op,e1),skc1) //(op e1 e3)
        val subt3 = App(App(op,e3),skc1) //(op e3 skc1)
        val subt4 = App(App(op,skc1),e3) //(op skc1 e3)
        val t8 = App(App(op,subt3),subt4) // (op (op e3 skc1) (op skc1 e3))
        val t9 = App(App(op,e1),e4) //(op e1 e4)
        val t10 = App(App(op,e3),e1) //(op e3 e1)
        
        val eq1 = EqW(t7,e1) // (op e1 e3) = e1)
        val eq2 = EqW(e4,t6) // (e4 = (op e4 e3))
        val eq3 = EqW(t8,e3) // ((op (op e3 skc1) (op skc1 e3)) = e3)
        val eq4 = EqW(e1,skc1) // (e1 = skc1)
        val eq5 = EqW(e3,t5) // (e3 = (op e1 e4))
        val eq6 = EqW(e4,t10) // (e4 = (op e3 e1))
        val eq7 = EqW(t7,subt4)// ((op e1 e3) = (op skc1 e3))
        val eq8 = EqW(e4,t1) //(e4 = (op (op e4 skc1) (op skc1 e4)))
        val eq9 = EqW(t5,subt2) //((op e1 e4) = (op skc1 e4))
        val allEqs = List(eq1,eq2,eq3,eq4,eq5,eq6,eq7,eq8,eq9)
        
        println(allEqs)
        
        con = con.addAll(allEqs)
        con = con.updateLazy
        val path = con.explain(t2,t6)
        val proof = path.get.toProof.get
        println(path)
        println(proof)
        println(path.get.originalEqs)
        
      }
      case 5 => {
        //((op e3 e1),(op e3 e3)) 
        //((e3 = (op e4 e4)), (e4 = skc1), (e4 = (op e3 e1)), ((op e4 e4) = (op skc1 e4)), (e4 = (op (op e4 skc1) (op skc1 e4)))
        
        val t1 = App(App(op,e4),e4) //(op e4 e4)
        val t2 = App(App(op,e3),e1) //(op e3 e1)
        val t3 = App(App(op,skc1),e4) // (op skc1 e4)
        val subt1 = App(App(op,e4),skc1) // (op e4 skc1)
        val t4 = App(App(op,subt1),t3) //(op (op e4 skc1) (op skc1 e4))
        
        val t5 = App(App(op,e3),e3) //(op e3 e3)
        
        val eq1 = EqW(e3,t1)
        val eq2 = EqW(e4,skc1)
        val eq3 = EqW(e4,t2)
        val eq4 = EqW(t1,t3)
        val eq5 = EqW(e4,t4)
        val allEqs = List(eq1,eq2,eq3,eq4,eq5)
        
        println(allEqs)
        
        con = con.addAll(allEqs)
        println(con.g)
//        con = con.resolveDeducedQueue
//        println("XXXXXXXXXXXXXXXXXX BEFORE ADDING")
        con = con.addNode(t5)
//        println("XXXXXXXXXXXXXXXXXX AFTER ADDING")
        val path = con.explain(t5,t2)
        
//        println(path.get.toProof)
        
        val path2 = con.explain(e3,subt1)
        println(path2)
//        println(path2.get.toProof)
        
//        println(con.g)
        
//        println(dij(e1,e1,con.g))
        
        println(path)
        println("origEqs: " + path.get.originalEqs)
//        println("transitivity chain:\n" + path.get.transChainProof.get)
        println("BUILDING PROOF")
        val proof = path.get.toProof.get
        println("full proof:\n" + proof)
        println(ProofTreeCNewNew(proof))
      }
      case 6 => {
        val op = new Var("op",Arrow(t,Arrow(t,t)))
        val e3 = new Var("e3",t)
        val e4 = new Var("e4",t)
        val skc1 = new Var("skc1",t)
        
        val t1 = App(App(op,e4),e4) //(op e4 e4)
        val t2 = App(App(op,e4),skc1) // (op e4 skc1)
        
        val eq1 = EqW(e3,t1)
        val eq2 = EqW(e4,skc1)
        val allEqs = List(eq1,eq2)
        
        con = con.addAll(allEqs)
        con = con.addNode(t2)
        
        val path = con.explain(e3,t2)
        println(path.get.toString(false))
        println("transitivity chain:\n" + path.get.toProof.get)
      }
    }
  }
}