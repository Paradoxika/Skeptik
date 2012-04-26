package ResK

object proofs {
  import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
  import scala.collection.mutable.Stack
//  import scala.collection.immutable.{Map, HashMap => IMap}
  import ResK.judgments._
  import ResK.expressions._
  import ResK.expressions.algorithms._
  import ResK.formulas._
  import ResK.positions._
  import ResK.utilities.prettyPrinting._
  
  abstract class Proof[+J <: Judgment](val premises: List[Proof[J]]) {
    def conclusion : J
    def name = ""
    def parameters = Nil
    override def toString = {
      var counter = 0; var result = "";
      def visitNode(n:Proof[J],r:List[Int]): Int = {
        counter += 1
        result += counter.toString + ": {" + n.conclusion + "} \t:" +
                  n.name + "(" + listToCSVString(r) + ")[" + listToCSVString(parameters) + "]\n"
        counter
      }
      proofs.traversal.topDown(this,visitNode)
      result
    }
  }

  abstract class SequentProof(override val premises: List[SequentProof],
                              val auxFormulas: Map[SequentProof,Sequent]) 
  extends Proof[Sequent](premises) {
    require(premises.forall(p => p.conclusion supersequentOf auxFormulas(p))) 
    // ancestry returns the subsequent of the given premise's conclusion
    // containing only ancestors of the given formula
    def ancestry(f: E, premise: SequentProof): Sequent = {
      if (mainFormulas contains f) activeAncestry(f, premise)
      else contextAncestry(f,premise)
    } 
    def activeAncestry(f: E, premise: SequentProof): Sequent
    def contextAncestry(f: E, premise: SequentProof): Sequent
    def mainFormulas : Sequent
    def conclusionContext : Sequent
    // The lazy modifier for "conclusion" is very important, 
    // because "conclusion" calls methods that will only be overriden by subtraits and subclasses.
    override lazy val conclusion = mainFormulas ++ conclusionContext
  }
  
  trait SingleMainFormula extends SequentProof {
    def mainFormula : E
    override def activeAncestry(f:E,premise:SequentProof) = {
      require(f == mainFormula); require(premises contains premise)
      auxFormulas.getOrElse(premise,Sequent())
    }
  }
  
  trait Left  extends SingleMainFormula {override def mainFormulas = Sequent(mainFormula,Nil)}
  trait Right extends SingleMainFormula {override def mainFormulas = Sequent(Nil,mainFormula)}
 
  trait NoMainFormula extends SequentProof {
    override def mainFormulas = Sequent()
    override def activeAncestry(f: E, premise: SequentProof) = throw new Exception("the given formula cannot be the main formula of this inference, because this inference has no main formula.")
  }
 
  
  trait NoImplicitContraction extends SequentProof {
    override def conclusionContext: Sequent = {
      val premiseContexts = premises.map(p => p.conclusion -- auxFormulas(p))
      premiseContexts match {
        case h::t => (h /: t)((s1,s2) => s1 ++ s2)
        case Nil => Sequent()
      }
    }
    override def contextAncestry(f: E, premise: SequentProof): Sequent = {
      require(conclusionContext contains f)
      require(premises contains premise)
      if (premise.conclusion.ant contains f) Sequent(f,Nil)
      else if (premise.conclusion.suc contains f) Sequent(Nil,f)
      else Sequent(Nil,Nil)
    } 
  }
  
  trait ImplicitContraction extends SequentProof {
    private val contextAndAncestryAux: (Sequent, MMap[(E,SequentProof),Sequent]) = {
      val context = premises.map(p => (p -> (p.conclusion -- auxFormulas(p)))).toMap
      val antSeen = new MSet[String] 
      val antDuplicates = new MSet[String]
      val sucSeen = new MSet[String] 
      val sucDuplicates = new MSet[String]
      for (p <- premises) {
        for (f <- context(p).ant) {
          if (antSeen contains f.stringRep) antDuplicates += f.stringRep
          else antSeen += f.stringRep
        }
        for (f <- context(p).suc) {
          if (sucSeen contains f.stringRep) sucDuplicates += f.stringRep
          else sucSeen += f.stringRep
        }          
      }
      
      val contextAncestryMap = new MMap[(E,SequentProof),Sequent] // stores the ancestor relation
      val conclusionContextAnt = new MSet[E] // stores the formulas that will go into the antecedent of the conclusion context
      val conclusionContextSuc = new MSet[E] // stores the formulas that will go into the succedent of the conclusion context
      val descendantsForAntDuplicates = new MMap[String,E] // stores the new copy that will serve as the contraction for several duplicates in the antecedent.
      val descendantsForSucDuplicates = new MMap[String,E] // stores the new copy that will serve as the contraction for several duplicates in the succedent.
      for (p <- premises) {
        for (f <- context(p).ant) {
          val descendant:E = {
            if (antDuplicates contains f.stringRep) {
              if (descendantsForAntDuplicates contains f.stringRep) {
                descendantsForAntDuplicates(f.stringRep)
              }
              else {
                val desc = f.copy
                descendantsForAntDuplicates += (f.stringRep -> desc)
                desc
              }     
            }
            else f 
          }
          conclusionContextAnt += descendant
          contextAncestryMap += ((descendant,p) -> Sequent(f,Nil))
        }
        for (f <- context(p).suc) {
          val descendant:E = {
            if (sucDuplicates contains f.stringRep) {
              if (descendantsForSucDuplicates contains f.stringRep) {
                descendantsForSucDuplicates(f.stringRep)
              }
              else {
                val desc = f.copy
                descendantsForSucDuplicates += (f.stringRep -> desc)
                desc
              }     
            }
            else f 
          }
          conclusionContextSuc += descendant
          contextAncestryMap += ((descendant,p) -> Sequent(Nil,f))
        }         
      }
      (Sequent(conclusionContextAnt.toList,conclusionContextSuc.toList), contextAncestryMap)
    }
   
    override val conclusionContext = contextAndAncestryAux._1
    override def contextAncestry(f: E, premise: SequentProof): Sequent = {
      require(conclusionContext contains f)
      require(premises contains premise)
      contextAndAncestryAux._2.getOrElse((f,premise),Sequent(Nil,Nil))
    } 
  }  
  
  
  class Axiom(override val mainFormulas: Sequent) extends SequentProof(Nil,Map()) 
  with NoImplicitContraction {
    override def activeAncestry(f: E, premise: SequentProof) = throw new Exception("Active formulas in axioms have no ancestors.")
    override def name = "Ax"
  }
  
  class AndL(val premise:SequentProof, val auxL:E, val auxR:E) 
  extends SequentProof(premise::Nil, Map(premise -> Sequent(auxL::auxR::Nil,Nil)))
  with SingleMainFormula with Left with NoImplicitContraction{
    override val mainFormula = And(auxL,auxR)
    override def name = "AndL"
  }
  
  class AndR(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E) 
  extends SequentProof(leftPremise::rightPremise::Nil,
                       Map(leftPremise -> Sequent(Nil,auxL), rightPremise -> Sequent(Nil,auxR))) 
  with NoImplicitContraction with SingleMainFormula with Right  {
    override val mainFormula = And(auxL,auxR)
    override def name = "AndR"
  }
  
  class AllL(val premise:SequentProof, val aux:E, val v:Var, val pl:List[Position]) 
  extends SequentProof(premise::Nil,Map(premise -> Sequent(aux,Nil)))
  with SingleMainFormula with Left with NoImplicitContraction {
    override val mainFormula = All(aux,v,pl)
    override def name = "AllL"
  }
 
  class AllR(val premise:SequentProof, val aux:E, val v:Var, val eigenvar:Var) 
  extends SequentProof(premise::Nil,Map(premise -> Sequent(Nil,aux)))   
  with SingleMainFormula with Right with NoImplicitContraction { 
    override val mainFormula = All(aux,v,eigenvar)
    require(!conclusion.ant.exists(e => (eigenvar occursIn e)) &&
            !conclusion.suc.exists(e => (eigenvar occursIn e)))
    override def name = "AllR"
  }
  
  class Cut(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E)
  extends SequentProof(leftPremise::rightPremise::Nil,
                       Map(leftPremise -> Sequent(Nil,auxL),
                           rightPremise -> Sequent(auxR,Nil)))
  with NoImplicitContraction with NoMainFormula {
    require(auxL =*= auxR)
    override def name = "Cut"
  }
  
  class CutIC(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E)
  extends SequentProof(leftPremise::rightPremise::Nil,
                       Map(leftPremise -> Sequent(Nil,auxL),
                           rightPremise -> Sequent(auxR,Nil))) 
  with ImplicitContraction with NoMainFormula {
    require(auxL =*= auxR)
    override def name = "CutIC"
  }
  
  class R(val leftPremise:SequentProof, val rightPremise:SequentProof, 
            val auxL:E, val auxR:E)
  extends SequentProof(leftPremise::rightPremise::Nil,
                       Map(leftPremise -> Sequent(Nil,auxL),
                           rightPremise -> Sequent(auxR,Nil)))
  with NoMainFormula {
    val unifier = unify((auxL,auxR)::Nil) match {
      case None => throw new Exception("Resolution: given premise clauses are not resolvable.")
      case Some(u) => u
    }
    private val ancestryMap = new MMap[(E,SequentProof),Sequent]
    override val conclusionContext = {
      def descendant(e:E, p:SequentProof, anc: Sequent) = {val eS = (e/unifier); ancestryMap += ((eS,p) -> anc); eS }
      val antecedent = leftPremise.conclusion.ant.map(e=>descendant(e,leftPremise,Sequent(e,Nil))) ++ 
                      (rightPremise.conclusion.ant - auxR).map(e=>descendant(e,rightPremise,Sequent(e,Nil)))
      val succedent = (leftPremise.conclusion.suc - auxL).map(e=>descendant(e,leftPremise,Sequent(Nil,e))) ++ 
                      rightPremise.conclusion.suc.map(e=>descendant(e,rightPremise,Sequent(Nil,e)))
      Sequent(antecedent,succedent)
    }
    override def contextAncestry(f:E,premise:SequentProof) = {
      require(conclusion contains f)
      require(premises contains premise)
      ancestryMap.getOrElse((f,premise),Sequent())
    }
    override def name = "R"
  }
  

  object R {
    def apply(leftPremise:SequentProof, rightPremise:SequentProof, auxL:E, auxR:E) = new R(leftPremise, rightPremise, auxL, auxR)
    def apply(leftPremise:SequentProof, rightPremise:SequentProof, findL:E=>Boolean, findR:E=>Boolean) = {
      new R(leftPremise, rightPremise,
                     leftPremise.conclusion.suc.find(findL).get,  //ToDo: Catch Exception
                     rightPremise.conclusion.ant.find(findR).get) //ToDo: Catch Exception
    }
    def apply(leftPremise:SequentProof, rightPremise:SequentProof) = {
      def isUnifiable(p:(E,E)) = unify(p::Nil) match {
          case None => false
          case Some(_) => true
        }
      val unifiablePairs = (for (auxL <- leftPremise.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL,auxR)).filter(isUnifiable)
      if (unifiablePairs.length > 0) { 
        val (auxL,auxR) = unifiablePairs(0)
        new R(leftPremise, rightPremise, auxL, auxR)
      }
      else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
      else throw new Exception("Resolution: the resolvent is ambiguous.") // ToDo
    }
    def unapply(p:SequentProof) = p match {
      case p: R => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
      case _ => None
    }
  }

 

  object Axiom {
    def apply(conclusion: Sequent) = new Axiom(conclusion)
    def unapply(p: SequentProof) = p match {
      case p: Axiom => Some(p.conclusion)
      case _ => None
    }
  } 

  object AllR {
    def apply(premise:SequentProof, aux:E, v:Var, eigenvar:Var) = new AllR(premise,aux,v,eigenvar)
    def unapply(p: SequentProof) = p match {
      case p: AllR => Some((p.premise,p.aux,p.v,p.eigenvar))
      case _ => None
    }
  } 
  object AllL {
    def apply(premise:SequentProof, aux:E, v:Var, pl:List[Position]) = new AllL(premise,aux,v,pl)
    def unapply(p: SequentProof) = p match {
      case p: AllL => Some((p.premise,p.aux,p.v,p.pl))
      case _ => None
    }
  } 
  object AndL {
    def apply(premise: SequentProof, auxL:E, auxR:E) = new AndL(premise,auxL,auxR)
    def unapply(p: SequentProof) = p match {
      case p: AndL => Some((p.premise,p.auxL,p.auxR))
      case _ => None
    }
  }
  object AndR {
    def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new AndR(leftPremise,rightPremise,auxL,auxR)
    def unapply(p: SequentProof) = p match {
      case p: AndR => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
      case _ => None
    }
  }
  object Cut {
    def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new Cut(leftPremise,rightPremise,auxL,auxR)
    def unapply(p: SequentProof) = p match {
      case p: Cut => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
      case _ => None
    }
  }
  object CutIC {
    def apply(leftPremise: SequentProof, rightPremise: SequentProof, auxL:E, auxR:E) = new CutIC(leftPremise,rightPremise,auxL,auxR)
    def apply(premise1:SequentProof, premise2:SequentProof) = {
      def findPivots(p1:SequentProof, p2:SequentProof): Option[(E,E)] = {
        for (auxL <- p1.conclusion.suc; auxR <- p2.conclusion.ant) if (auxL =*= auxR) return Some(auxL,auxR)
        return None
      }
      findPivots(premise1,premise2) match {
        case Some((auxL,auxR)) => new CutIC(premise1,premise2,auxL,auxR)
        case None => findPivots(premise2,premise1) match {
          case Some((auxL,auxR)) => new CutIC(premise2,premise1,auxL,auxR)
          case None => throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
        }
      }
    }
    def unapply(p: SequentProof) = p match {
      case p: CutIC => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
      case _ => None
    }
  }
  
  
  object traversal {
    import scala.collection.mutable.Queue
    import scala.collection.mutable.Stack
    import scala.collection.mutable.{HashSet => MSet}
  
    
    
//    abstract class ATree[+A,+B <: ATree[A,B]](val parents: List[B])
//    class MyTree(parents:List[MyTree]) extends ATree[String,MyTree](parents)
//    case class Leaf(a:String) extends MyTree(Nil)
//    case class Node(l:MyTree,r:MyTree) extends MyTree(l::r::Nil)
//    
//    def traverse[A, B <: ATree[A,B]](t: B, f: B => Unit): Unit = {
//      f(t)
//      for (p <- t.parents) traverse[A,B](p, f)
//    }
//    
//    val example = Node(Leaf("a"),Leaf("b"))
//    
//    def doSomething(t:MyTree) = println(t)
//    
//    traverse[String,MyTree](example, doSomething)
    
    //def doS[A](t:ATree[A]) = println(t.asInstanceOf[MyTree])
    
    //traverse(example, doS)
    
    
    def topologicallySort[J <: Judgment](roots:Proof[J]*) = {
      val topDown = new Queue[Proof[J]]
      val bottomUp = new Stack[Proof[J]]
      val visited = new MSet[Proof[J]]
      def visit(p:Proof[J]):Unit = if (!visited(p)){
        visited += p
        p.premises.foreach(premise => visit(premise))
        topDown += p
        bottomUp.push(p)
      }
      roots foreach { root => visit(root) }
      (bottomUp,topDown)
    }
    
    
    
    def topDown[J <: Judgment ,X](p:Proof[J], f:(Proof[J],List[X])=>X):Unit = topDownT(f,topologicallySort(p)._2)  
    def topDownT[J <: Judgment ,X](f:(Proof[J],List[X])=>X, 
                                  nodes:TraversableOnce[Proof[J]]):Unit = {
      val resultFrom : MMap[Proof[J],X] = MMap()

      nodes.foreach(node => {
        val result = f(node, node.premises.map(premise => resultFrom(premise)))
        resultFrom += (node -> result)       
      })
    }
    

    def bottomUp[J <: Judgment,X](p:Proof[J], f:(Proof[J],List[X])=>X):Unit = bottomUpT(f,topologicallySort(p)._1)  
    def bottomUpT[J <: Judgment,X](f:(Proof[J],List[X])=>X, 
                                   nodes:TraversableOnce[Proof[J]]):Unit = {
      val resultsFromChildrenOf : MMap[Proof[J],List[X]] = MMap()

      nodes.foreach(node => {
        val result = f(node, resultsFromChildrenOf.getOrElse(node,Nil))
        resultsFromChildrenOf -= node
        node.premises.foreach(premise => {
            resultsFromChildrenOf += 
              (premise -> (result::resultsFromChildrenOf.getOrElse(premise,Nil)))           
        })        
      })
    }
    
    
  }
}

