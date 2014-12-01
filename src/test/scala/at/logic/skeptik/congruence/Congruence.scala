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
import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class CongruenceSpecification extends SpecificationWithJUnit {
    val testcase = 5
    
    val ty = o
    
    val a = new Var("a",ty)
    val a1 = new Var("a1",ty)
    val a2 = new Var("a2",ty)
    val a3 = new Var("a3",ty)
    val b = new Var("b",ty)
    val b1 = new Var("b1",ty)
    val b2 = new Var("b2",ty)
    val b3 = new Var("b3",ty)
    val c = new Var("c",ty)
    val c1 = new Var("c1",ty)
    val c2 = new Var("c2",ty)
    val c3 = new Var("c3",ty)
    
    val d = new Var("d",ty)
    val e = new Var("e",ty)
    
    val f = new Var("f",Arrow(ty,ty))
    
    val f1 = new Var("f",Arrow(ty,Arrow(ty,ty)))
    
    val x = new Var("x",Arrow(ty,ty))
    
    val op = new Var("op",Arrow(ty,Arrow(ty,ty)))
    val e4 = new Var("e4",ty)
    val skc1 = new Var("skc1",ty)
    val e3 = new Var("e3",ty)
    val e1 = new Var("e1",ty)
    
    def origSubterms(term: E): Seq[E] = (term,term.t) match {
      case (App(u,v),Arrow(_,_)) => origSubterms(v) ++ origSubterms(u)
      case (_, Arrow(_,_)) => Seq()
      case (t, _) => Seq(term)
    }

    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val reflMap = MMap[E,N]()

    var con: AbstractCongruence = FibCon(eqReferences)
    var path: Option[EquationPath] = None
    var isCongruent = false
    
    testcase match {
      
      case -8 => {
        val t1 = App(App(f1,a),e);
        val t2 = App(App(f1,d),e);
        con = con.addEquality(EqW(c1,t1));
        con = con.addEquality(EqW(a,c));
        con = con.addEquality(EqW(b,c));
        con = con.addEquality(EqW(c,d));
        con = con.addEquality(EqW(c2,t2));
        con = con.updateLazy
        path = con.explain(c1, c2)
        isCongruent = con.isCongruent(c1, c2)
      }
      
      case -7 => {
        con = con.addEquality(EqW(a,b)).updateLazy
        path = con.explain(a, b)
        isCongruent = con.isCongruent(a, b)
      }
      
      case -6 => {
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,t1),b)
        con = con.addEquality(EqW(a,t1)).addNode(t2)
        con = con.updateLazy
        path = con.explain(t1, t2)
        isCongruent = con.isCongruent(t1, t2)
      }
      
      case -5 => {
        con = con.addEquality(EqW(a,b)).addEquality(EqW(b,c)).addEquality(EqW(c,e)).addEquality(EqW(e,d))
        con = con.updateLazy
        path = con.explain(a, d)
        isCongruent = con.isCongruent(a, d)
      }
      
      case -4 => {
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,b),a)
        con = con.addEquality(EqW(a,c)).addEquality(EqW(b,c)).addNode(t1).addNode(t2)
        con = con.updateLazy
        path = con.explain(t1,t2)
        isCongruent = con.isCongruent(t1, t2)
      }
      
      case -3 => {
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,b),a)
        con = con.addEquality(EqW(a,b,false)).addEquality(EqW(b,a,false)).addNode(t1).addNode(t2)
        con = con.updateLazy
        path = con.explain(t1,t2)
        isCongruent = con.isCongruent(t1, t2)
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
        con = con.addEquality(eq1).addNode(v1).addNode(v2)
        con = con.updateLazy
        path = con.explain(v1, v2)
        isCongruent = con.isCongruent(v1, v2)
      }
      
      case -1 => {
        val s1 = App(f1,a)
        val s2 = App(f1,c)
        val t1 = App(App(f1,a),b)
        val t2 = App(App(f1,c),d)
        val eq1 = EqW(a,e)
        val eq2 = EqW(b,d)
        val eq3 = EqW(c,e)
        con = con.addEquality(eq1).addEquality(eq2).addEquality(eq3).addNode(t1).addNode(t2)
        con = con.updateLazy
        path = con.explain(t1, t2)
        isCongruent = con.isCongruent(t1, t2)
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
        
        path = con.explain(e,d)
        isCongruent = con.isCongruent(t1, t2)
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
        path = con.explain(a,c)
        isCongruent = con.isCongruent(a,c)
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
        path = con.explain(a,c)
        isCongruent = con.isCongruent(a, c)
      }
      
      case 3 => {
        //g(l,h) = d, c = d, g(l,d) = a, e = c, e = b, b = h
        
        val g = new Var("g",Arrow(ty,Arrow(ty,ty)))
        val l = new Var("l",ty)
//        val i = new Var("i",Arrow(i,i))
        val h = new Var("h",ty)
        
        val t1 = App(App(g,l),h)
        val t2 = App(App(g,l),d)
        
        val eqs = List(EqW(t1,d),EqW(t2,a),EqW(c,d),EqW(e,c),EqW(e,b),EqW(b1,b),EqW(b1,h))
        con = con.addAll(eqs).updateLazy
        path = con.explain(a,b)
        isCongruent = con.isCongruent(a, b)
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
        
        
        con = con.addAll(allEqs)
        con = con.updateLazy
        path = con.explain(t2,t6)
        isCongruent = con.isCongruent(t2, t6)
        
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
        
        con = con.addAll(allEqs)
        con = con.addNode(t5)
        con = con.updateLazy
        path = con.explain(t5,t2)
        isCongruent = con.isCongruent(t5, t2)
      }
      case 6 => {
        val op = new Var("op",Arrow(ty,Arrow(ty,ty)))
        val e3 = new Var("e3",ty)
        val e4 = new Var("e4",ty)
        val skc1 = new Var("skc1",ty)
        
        val t1 = App(App(op,e4),e4) //(op e4 e4)
        val t2 = App(App(op,e4),skc1) // (op e4 skc1)
        
        val eq1 = EqW(e3,t1)
        val eq2 = EqW(e4,skc1)
        val allEqs = List(eq1,eq2)
        
        con = con.addAll(allEqs)
        con = con.addNode(t2)
        con = con.updateLazy
        path = con.explain(e3,t2)
        isCongruent = con.isCongruent(e3, t2)
      }
      
    }
    "Congruence " should {
        "deduce that terms are congruent " in {
          isCongruent
        }
        "produce a proof " in {
          path match {
            case None => false
            case Some(p) => {
              p.toProof match {
                case None => false
                case Some(proof) => true
              }
            }
          }
        }
      }
}