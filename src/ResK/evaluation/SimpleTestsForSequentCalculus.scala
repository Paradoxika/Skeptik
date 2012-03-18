package ResK.evaluation

import ResK.expressions._
import ResK.judgments._
import ResK.proofs._
import ResK.formulas._
import ResK.formulaAlgorithms._


object Main {

  def main(args: Array[String]): Unit = {
    
    println("Lambda Terms:")
    println()
    
    val e1 = App(Var("P", i -> o), Var("a", i))
    val e2 = App(Var("P", i -> o), Var("a", i))
    val e3 = Abs(Var("a", i), e2.copy)
    
    println("e1 :" + e1 )
    println("e2 :" + e2 )
    println("e3 :" + e3 )
    
    println()
    println()
    println("Syntatic Equality versus Object Equality:")
    println()
    println("e1 == e2 :" + e1 == e2)
    println("e1 syntaticEquals e2 :" + (e1 syntaticEquals e2))
    println("e1 =*= e2 :" + (e1 =*= e2))
    println("e1 == e1.copy :" + e1 == e1.copy)
    println("e1 =*= e1.copy :" + (e1 =*= e1.copy))
    
    println()
    println()    
    println("Formulas:")
    println()
    
    val e = Atom(Var("Q", i -> (i -> o)), Var("a", i)::Var("b", i)::Nil)
    println("e : " + e)
    e match {
      case Atom(p,l) => {println(p);println(l)}
      case _ => println("error")
    }
    
    
    val f = And(e, e.copy)
    val f2 = And(e, e)
    println("f : " + f)
    
    
    val Pa = App(Var("P", i -> o), Var("a", i))
    def gA(x:E) = Pa
    val g = deepApply(gA,f,1::Nil)
    println("g : " + g)
    
    val h = All(g,Var("x",i),(2::2::Nil)::Nil)
    println("h : " + h)
    
    val j = All(Pa, Var("v", i), Var("a", i))
    println("j : " + j)
 
    
    println()
    println()   
    println("Alpha Equality:")
    println()
    
    def v(n:String, t:T) = Var(n,t)
    
    val k = All(v("x",i), App(v("P", i -> o), v("x",i)))
    val l = All(v("y",i), App(v("P", i -> o), v("y",i)))
    println("k : " + k)
    println("l : " + l)
    println("k == l :" + k == l)
    println("k =*= l :" + (k =*= l))
    println("k alphaEquals l :" + (k alphaEquals l))
    println("k =+= l :" + (k =+= l))
    
    
    
    println()
    println()   
    println("Sequent Calculus Proofs:")
    println()
    
    val a = App(Var("P", i -> o), Var("a", i))
    val b = App(Var("P", i -> o), Var("b", i))
    val c = App(Var("P", i -> o), Var("c", i))
    val d = Atom(Var("P", i -> o), Var("d", i)::Nil)
   
    def S(l1:List[E],l2:List[E]) = Sequent(l1,l2)

    
    val p1 = AndL(AndR(Axiom(S(a::Nil,b::Nil)),
                       Axiom(S(c::Nil,d::Nil)),
                       b,
                       d),
                  a,
                  c)
    
    val p2 = AllL(p1,p1.conclusion.ant(0),Var("v",i),(1::1::Nil)::Nil)    
    val p3 = AllR(p2,p2.conclusion.suc(0),Var("z",i),Var("d", i))
    
    println(p3)

    println()
    println()
    
    val (a1,a2,b1,b2,c1,c2) = (a.copy,a.copy,b.copy,b.copy,c.copy,c.copy)
    val p4 = CutIC(Axiom(S(a1::Nil,b1::c1::Nil)),
                   Axiom(S(a2::b2::Nil,c2::Nil)),
                   b1,
                   b2)
    println("p4: \n" + p4)

    println()
    println()
    
    val p5 = Cut(Axiom(S(a1::Nil,b1::c1::Nil)),
                 Axiom(S(a2::b2::Nil,c2::Nil)),
                 b1,
                 b2)
    println("p5: \n" + p5)
    
    
    println()
    println()   
    println("Unification: ")
    println()
    
    import ResK.expressions.algorithms._
    
    val z = Var("z",i->o,"eigen")
    val P = v("P",i->o)
    val w = v("u",i)
    println(unify((App(z,w),App(P,w.copy))::Nil))
    println(unify((App(z,w),App(Abs(v("x",i),App(P,v("x",i))),w.copy))::Nil))

    
    println()
    println()   
    println("Propositional Resolution: ")
    println()
    
    val AiBC = Axiom(S(v("A",o)::Nil, v("B",o)::v("C",o)::Nil))
    val ABi = Axiom(S(v("A",o)::v("B",o)::Nil, Nil))
    val Ci = Axiom(S(v("C",o)::Nil, Nil))
    val iA = Axiom(S(Nil, v("A",o)::Nil))
 
    
    println()
    println()   
    println("Higher-order Resolution: ")
    println()
    
    val rProof = R(R(R(iA,AiBC),
                     R(iA,ABi)),
                   Ci)
    println(rProof)
    
    val hAiBC = Axiom(S(Atom(v("A",i->o),v("d",i)::Nil)::Nil, Atom(v("B",i->o),v("c",i)::Nil)::v("C",o)::Nil))
    val hABi = Axiom(S(Atom(v("A",i->o),Var("y",i,"eigen")::Nil)::Atom(v("B",i->o),Var("y",i,"eigen")::Nil)::Nil, Nil))
    val hCi = Axiom(S(Var("X",o,"eigen")::Nil, Nil))
    val hiA = Axiom(S(Nil, Atom(v("A",i->o),Var("z",i,"eigen")::Nil)::Nil))
    
    val hrProof = R(R(hiA,
                      R(hiA,
                        R(hAiBC,hABi))),
                    hCi)
    println(hrProof)
    
    import ResK.proofs.traversal._;
    
    val (up, down) = topologicallySort(hrProof)
    println()
    up.foreach(n => println(n.conclusion))
    println()
    down.foreach(n => println(n.conclusion))
    println()
    bottomUp[Sequent,Any](hrProof,(p,l)=>{println(p.conclusion)})
    println()
    topDown[Sequent,Any](hrProof,(p,l)=>{println(p.conclusion)})  
  }

}
