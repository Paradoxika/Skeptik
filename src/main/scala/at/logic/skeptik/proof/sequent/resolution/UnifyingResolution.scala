package at.logic.skeptik.proof.sequent
package resolution

import collection.mutable.{HashMap => MMap, Set => MSet}
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.unifier.{MartelliMontanari => unify}
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }



class UnifyingResolution(val leftPremise:SequentProofNode, val rightPremise:SequentProofNode,
          val auxL:E, val auxR:E)(implicit unifiableVariables: MSet[Var])
extends SequentProofNode with Binary
with NoMainFormula {

  def leftAuxFormulas: SeqSequent = ???
  def rightAuxFormulas: SeqSequent = ???
  
  // When a unifiable variable X occurs in both premises, 
  // we must rename its occurrences in one of the premises to a new variable symbol Y
  // not occurring in any premise
  val (leftPremiseR :SequentProofNode, rightPremiseR: SequentProofNode, auxLR, auxRR) = {    
    // For example, suppose we are trying to resolve:
    
    //  p(X) |- q(a)     with    q(X) |- 
    
    // note that all variables are assumed to be universally quantified.
    // therefore, the X in the left premise has nothing to do with the X in the right premise.
    
    //check if there is a variable in both    
    def getSetOfVarsFromPremise(pn: SequentProofNode) = {
      def formula = pn.mainFormulas
      def ante = formula.ant
      def succ = formula.suc
      
      
      def investigateExpr(e: E): Set[Var] = e match {
      case App(e1, e2) => {
        investigateExpr(e1).union(investigateExpr(e2))
      }
      case Abs(v,e1) => {
        investigateExpr(v).union(investigateExpr(e1))
      }
      case v: Var => Set[Var](v)
      }
    
      
      def getSetOfVarsFromExpr(e: Seq[E]): Set[Var] = {
        if(e.length > 1) { 
          investigateExpr(e.head)
          getSetOfVarsFromExpr(e.tail)
        } else if (e.length == 1) {
          investigateExpr(e.head)
        } else {
          Set[Var]()
        }
      }
      getSetOfVarsFromExpr(ante).union(getSetOfVarsFromExpr(succ))
    }

    val usedVars = getSetOfVarsFromPremise(leftPremiseR).intersect(getSetOfVarsFromPremise(rightPremiseR))

    
    
    
    // if we just resolve these two clauses we would get the following WRONG resolvent:
    
    // p(a) |- 
    
    // As a preprocessing step, it is necessary to rename the X's in one of the clauses to a variable symbol 
    // not occurring in any of the premises. For example:
    
    // p(Y) |- q(a)     with     q(X) |- 
    
    // Then we get the CORRECT resolvent:
    
    // p(Y) |- 
    
    // note that you must add the new symbol Y to the set of unifiable variables, if it is not already there.
    
    // to avoid the proliferation of new symbols, which could lead to memory issues, 
    // I recommend that you try to use symbols that are already in unifiableVariables (but not in any of the premises)
    // as much as possible.
    
    // In order to find the variables X that occur in both premises, 
    // I recommend that you create a function that will traverse a formula and return a set of its unifying variables.
    // then you take the intersection of the sets from each premise.
    
    // In order to replace a variable X by a new variable Y, you can use the existing code for substitutions in the 
    // at.logic.skeptik.expression.substitution.{mutable,immutable} packages. 
    // You can learn how to use substitutions by looking at the MartelliMontanari.
    
    // By the way, the substitution code is a good example of how you can traverse a formula using Scala's pattern matching.
    
    //Find, and assign a new name
    val availableVars = unifiableVariables.diff(usedVars)
    var replacement = null.asInstanceOf[Var] //TODO: better way to do this?
    if(availableVars.size >= 1){
      //use one thats available
      replacement = availableVars.head
    } else {
      replacement = new Var("SomeNewName", i) //TODO: generate names in a much smarter way
    }
    
    //TODO: check that usedVars.head is valid (i.e. usedVars.length > 1)
    //TODO: make replacements for every variable in usedVars
    val sub = Substitution(replacement -> usedVars.head)//TODO: check: is this the right order?
    
    //Substitute the new name into one of the premises; let say the left one //TODO: check: does this matter?
    val newAnt = for(a <- leftPremiseR.mainFormulas.ant) yield sub(a)
    val newSuc = for(a <- leftPremiseR.mainFormulas.suc) yield sub(a)
    
    val seqOut = Sequent(newAnt.head)(newSuc.head) //TODO: not just heads, but the entire sequences
    
    val axOut = Axiom(seqOut)
    //TODO: not sure if I can just use a new proof node; this one won't be in the proofMap of the parser. 
    //	Is that going to effect anything? Check.
    
    //TODO: update these with something suitable
    (axOut, rightPremise, auxL, auxR) // Nothing is done yet.
  }
  

  
  val mgu = unify((auxLR,auxRR)::Nil) match {
    case None => throw new Exception("Resolution: given premise clauses are not resolvable.")
    case Some(u) => {
      u
    }
  }
  override val conclusionContext = {
    val antecedent = leftPremiseR.conclusion.ant.map(e=>mgu(e)) ++
                    (rightPremiseR.conclusion.ant.filter(_ != auxR)).map(e=>mgu(e))
    val succedent = (leftPremiseR.conclusion.suc.filter(_ != auxL)).map(e=>mgu(e)) ++
                    rightPremiseR.conclusion.suc.map(e=>mgu(e))
    new Sequent(antecedent, succedent)
  }
}


object UnifyingResolution {
  def apply(leftPremise:SequentProofNode, rightPremise:SequentProofNode, auxL:E, auxR:E)(implicit unifiableVariables:MSet[Var]) = new UnifyingResolution(leftPremise, rightPremise, auxL, auxR)
  def apply(leftPremise:SequentProofNode, rightPremise:SequentProofNode)(implicit unifiableVariables:MSet[Var]) = {
    def isUnifiable(p:(E,E)) = unify(p::Nil)(unifiableVariables) match {
        case None => false
        case Some(_) => true
      }
    val unifiablePairs = (for (auxL <- leftPremise.conclusion.suc; auxR <- rightPremise.conclusion.ant) yield (auxL,auxR)).filter(isUnifiable)
    if (unifiablePairs.length > 0) {
      val (auxL, auxR) = unifiablePairs(0)
      new UnifyingResolution(leftPremise, rightPremise, auxL, auxR)
    }
    else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
    else throw new Exception("Resolution: the resolvent is ambiguous.")
  }
  def unapply(p:SequentProofNode) = p match {
    case p: UnifyingResolution => Some((p.leftPremise,p.rightPremise,p.auxL,p.auxR))
    case _ => None
  }
}
