package ResK

object proofs {
  import scala.collection.mutable.{HashMap => MMap}
  import ResK.judgments._
  import ResK.expressions._
  import ResK.expressions.algorithms._
  import ResK.formulas._
  import ResK.positions._
  
  abstract class Proof[T <: Judgment](val premises: List[Proof[T]]) {
    def conclusion : T
    def info = ""
    override def toString = {
      var counter = 0
      val visited = new MMap[Proof[T],Int]
      def toStringRec(p:Proof[T]):String = if (!visited.contains(p)) {
        val recResults = for (premise <- p.premises) yield toStringRec(premise)
        counter += 1
        visited += (p -> counter)
        val lastLine = counter.toString + ":  " + p.conclusion.toString + "   | " + p.info + " " +
                   ("" /: p.premises.map(q => visited(q)))((s1,s2) => s1 + s2 + " ") + "\n"
        val result = (recResults :\ lastLine)((s1,s2) => s1 + s2)
        return result
      } else return ""
      toStringRec(this)
    }
  }
  
  abstract class SequentProof(override val premises: List[SequentProof],
                              val auxFormulas: List[Sequent]) 
  extends Proof[Sequent](premises) {
    def mainFormulas = {
      def filterFormulasNotInPremises(l:List[E]) = l.filter(f => premises.forall(p => ! p.conclusion.contains(f) )) 
      Sequent(filterFormulasNotInPremises(conclusion.ant),filterFormulasNotInPremises(conclusion.suc))
    }
    def context = conclusion -- mainFormulas
    def ancestorsOf(f: E): List[Sequent] = {
      require(conclusion contains f)
      if (mainFormulas contains f) auxFormulas
      else (for (p <- premises) yield (if (p.conclusion.ant contains f) Sequent(f::Nil,Nil)
                                       else if (p.conclusion.suc contains f) Sequent(Nil,f::Nil)
                                       else Sequent(Nil,Nil) )).toList
    } 
  }
  
  class Axiom(override val conclusion: Sequent) extends SequentProof(Nil,Nil) {
    override def info = "Axiom"
  }
  
  class AndL(val premise:SequentProof, val auxL:E, val auxR:E) 
  extends SequentProof(premise::Nil, Sequent(auxL::auxR::Nil,Nil)::Nil) {
    require(premise.conclusion.ant.contains(auxL) && premise.conclusion.ant.contains(auxR))
    override lazy val conclusion = And(auxL,auxR) +: (premise.conclusion -- auxFormulas(0)) 
    override def info = "AndL"
  }
  
  class AndR(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E) 
  extends SequentProof(leftPremise::rightPremise::Nil,Sequent(Nil,auxL::Nil)::Sequent(Nil,auxR::Nil)::Nil) {
    require(leftPremise.conclusion.suc.contains(auxL) && rightPremise.conclusion.suc.contains(auxR))
    override lazy val conclusion = {
      ((leftPremise.conclusion -- auxFormulas(0)) ++
      (rightPremise.conclusion -- auxFormulas(1))) + And(auxL,auxR)
    }
    override def info = "AndR"
  }
  
  class AllL(val premise:SequentProof, val aux:E, val v:Var, val pl:List[Position]) 
  extends SequentProof(premise::Nil,Sequent(aux::Nil,Nil)::Nil) {
    require(premise.conclusion.ant.contains(aux))
    override lazy val conclusion = All(aux,v,pl) +: (premise.conclusion -- auxFormulas(0)) 
    override def info = "AllL"
  }
 
  class AllR(val premise:SequentProof, val aux:E, val v:Var, val eigenvar:Var) 
  extends SequentProof(premise::Nil,Sequent(Nil,aux::Nil)::Nil) {
    require(premise.conclusion.suc.contains(aux))
    override val conclusion = (premise.conclusion -- auxFormulas(0)) + All(aux,v,eigenvar) 
    require(!conclusion.ant.exists(e => (eigenvar occursIn e)) &&
            !conclusion.suc.exists(e => (eigenvar occursIn e)))
    override def info = "AllR"
  }
  
 
  
  class Resolution(val leftPremise:SequentProof, val rightPremise:SequentProof, val auxL:E, val auxR:E)
  extends SequentProof(leftPremise::rightPremise::Nil,Sequent(Nil,auxL::Nil)::Sequent(auxR::Nil,Nil)::Nil) {
    val unifier = unify((auxL,auxR)::Nil) match {
      case None => throw new Exception("Resolution: given premise clauses are not resolvable.")
      case Some(u) => u
    }
    private val ancestorMap = new MMap[E,E]
    override val conclusion = {
      def descendant(e:E) = {val eS = (e/unifier); ancestorMap += (eS -> e); eS }
      val antecedent = leftPremise.conclusion.ant.map(descendant) ++ 
                      (rightPremise.conclusion.ant - auxR).map(descendant)
      val succedent = (leftPremise.conclusion.suc - auxL).map(descendant) ++ 
                      rightPremise.conclusion.suc.map(descendant)
      Sequent(antecedent,succedent)
    }
    override def mainFormulas = Sequent(Nil,Nil)
    override def ancestorsOf(f:E) = {
      val ancestor = ancestorMap(f)
      if (conclusion.ant contains f) {
        if (leftPremise.conclusion.ant contains ancestor) Sequent(ancestor::Nil,Nil)::Sequent(Nil,Nil)::Nil
        else  Sequent(Nil,Nil)::Sequent(ancestor::Nil,Nil)::Nil
      }
      else if (conclusion.suc contains f) {
        if (leftPremise.conclusion.suc contains ancestor) Sequent(Nil,ancestor::Nil)::Sequent(Nil,Nil)::Nil
        else  Sequent(Nil,Nil)::Sequent(Nil,ancestor::Nil)::Nil
      }
      else throw new Exception("Resolution: formula does not occur in the conclusion.")
    }
    override def info = "Resolution"
  }

  object R {
    def apply(leftPremise:SequentProof, rightPremise:SequentProof, auxL:E, auxR:E) = new Resolution(leftPremise, rightPremise, auxL, auxR)
    def apply(leftPremise:SequentProof, rightPremise:SequentProof, findL:E=>Boolean, findR:E=>Boolean) = {
      new Resolution(leftPremise, rightPremise,
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
        new Resolution(leftPremise, rightPremise, auxL, auxR)
      }
      else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
      else throw new Exception("Resolution: the resolvent is ambiguous.") // ToDo
    }
    def unapply(p:SequentProof) = p match {
      case p: Resolution => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
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
  object Axiom {
    def apply(conclusion: Sequent) = new Axiom(conclusion)
    def unapply(p: SequentProof) = p match {
      case p: Axiom => Some(p.conclusion)
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
  
}

