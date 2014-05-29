package at.logic.skeptik.proof.sequent
package resolution

import collection.mutable.{ HashMap => MMap, Set => MSet }
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.judgment.immutable.SeqSequent
import at.logic.skeptik.proof.sequent.lk.{ R, Axiom, UncheckedInference }
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents
import at.logic.skeptik.parser.ProofParserSPASS

class UnifyingResolution(val leftPremise: SequentProofNode, val rightPremise: SequentProofNode,
  val auxL: E, val auxR: E)(implicit unifiableVariables: MSet[Var])
  extends SequentProofNode with Binary
  with NoMainFormula {

 
  
  def leftAuxFormulas: SeqSequent = ???
  def rightAuxFormulas: SeqSequent = ???

  //TODO: probably shouldn't use var
  var replacementInverse: List[Substitution] = List[Substitution]()//null.asInstanceOf[Substitution]
  
  // When a unifiable variable X occurs in both premises, 
  // we must rename its occurrences in one of the premises to a new variable symbol Y
  // not occurring in any premise
  val (leftPremiseR: SequentProofNode, rightPremiseR: SequentProofNode, auxLR: E, auxRR: E) = {
	(leftPremise, rightPremise, auxL, auxR)
	//By removing shared variables in the UnifyingResolution object, we don't need these variables. //TODO: check
    //fixShared(leftPremise, rightPremise, auxL, auxR, 0)
  }

  def fixShared(leftPremiseR: SequentProofNode, rightPremiseR: SequentProofNode, auxLRin: E, auxRRin: E, count: Int): (SequentProofNode, SequentProofNode, E, E) = {
        
    // For example, suppose we are trying to resolve:

    //  p(X) |- q(a)     with    q(X) |- 

    // note that all variables are assumed to be universally quantified.
    // therefore, the X in the left premise has nothing to do with the X in the right premise.

    //check if there is a variable in both  

    //    println(leftPremiseR)
    //    println(rightPremiseR)

    def getSetOfVarsFromPremise(pn: SequentProofNode) = {
   	  val ante = pn.conclusion.ant
   	  val succ = pn.conclusion.suc


      def investigateExpr(e: E): Set[Var] = e match {
        case App(e1, e2) => {
          investigateExpr(e1).union(investigateExpr(e2))
        }
        case Abs(v, e1) => {
          investigateExpr(v).union(investigateExpr(e1))
        }
        case v: Var => {
          //Only care if the variable is a capital         
          val hasLowerCase = v.name.exists(_.isLower)
          val notAnInt = v.name.charAt(0).isLetter
          if (!hasLowerCase && notAnInt) {
            Set[Var](v)
          } else {
            Set[Var]()
          }
        }
      }

      def getSetOfVarsFromExpr(e: Seq[E]): Set[Var] = {
        if (e.length > 1) {
          investigateExpr(e.head).union(getSetOfVarsFromExpr(e.tail))
        } else if (e.length == 1) {
          investigateExpr(e.head)
        } else {
          Set[Var]()
        }
      }
      getSetOfVarsFromExpr(ante).union(getSetOfVarsFromExpr(succ))
    }    
    
    val sharedVars = getSetOfVarsFromPremise(leftPremiseR).intersect(getSetOfVarsFromPremise(rightPremiseR))
        
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

    if (sharedVars.size > 0) {
      //Find, and assign a new name
      //first diff is so that we don't use a variable that is shared
      //second/third diff is so that we don't use a variable appearing in the formula already
      val availableVars = unifiableVariables.diff(sharedVars.union(getSetOfVarsFromPremise(leftPremiseR).union(getSetOfVarsFromPremise(rightPremiseR))))

      var replacement = null.asInstanceOf[Var] //TODO: better way to do this?
      if (availableVars.size >= 1) {
        //use one thats available
        replacement = availableVars.head
      } else {
        replacement = new Var("NEW" + count, i)
        unifiableVariables +=  new Var("NEW" + count, i)
      }
            
      val sub = Substitution(sharedVars.head -> replacement) //perform the replacement
//      println("UR sub: " + sub)
      //Keep track of the replacement, so we can reverse it when we're done 
      //TODO: remove, I think.
//      replacementInverse = replacementInverse ::: List(Substitution(replacement -> sharedVars.head))
      
      //Substitute the new name into one of the premises; let say the left one //TODO: check: does this matter?
      
      val newAnt = for (a <- leftPremiseR.conclusion.ant) yield sub(a)
      val newSuc = for (a <- leftPremiseR.conclusion.suc) yield sub(a)      
      
      
      //TODO: check that this is the right way to modify these expr's      
      val newAuxL = sub(auxLRin)
      
      val sA = addAntecedents(newAnt.seq.filter(_ != auxLRin).toList)
      val sS = addSuccedents(newSuc.seq.filter(_ != auxLRin).toList)

      
      val seqOut = sA union sS
      val axOut = Axiom(seqOut)
            
      //TODO: not sure if I can just use a new proof node; this one won't be in the proofMap of the parser. 
      //	Is that going to effect anything? Check.
                 
      fixShared(axOut, rightPremiseR, newAuxL, auxRRin, count + 1) //recursively call the function so that any more shared variables are also dealt with
    } else { //sharedVars.size  < 1
      (leftPremiseR, rightPremiseR, auxLRin, auxRRin) //no change
    }
  }
  

//  val mgu = unify(  ( {println(ProofParserSPASS.count + " mgu-B using auxLR " + auxLR +" and auxRR" + auxRR); auxLR} , auxRR) :: Nil) match {
  val mgu = unify( (auxLR, auxRR) :: Nil) match {    
    case None => {
      throw new Exception("Resolution: given premise clauses are not resolvable.")
    }
    case Some(u) => {
      u
    }
  }
  override val conclusionContext = {
    val antecedent = leftPremiseR.conclusion.ant.map(e => mgu(e)) ++
      (rightPremiseR.conclusion.ant.filter(_ != auxRR)).map(e => mgu(e))
    val succedent = (leftPremiseR.conclusion.suc.filter(_ != auxLR)).map(e => mgu(e)) ++
      rightPremiseR.conclusion.suc.map(e => mgu(e))
    new Sequent(antecedent, succedent)
  }
}

object UnifyingResolution {
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode, auxL: E, auxR: E)(implicit unifiableVariables: MSet[Var]) = new UnifyingResolution(leftPremise, rightPremise, auxL, auxR)
  def apply(leftPremise: SequentProofNode, rightPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]) = {
//    def isUnifiable(p: (E,E)) = unify( {
//    println(ProofParserSPASS.count + " mgu-A using p._1 " + p._1 +" and p._2 " + p._2)
//
//    if(ProofParserSPASS.count == 44){
//    println("HOPE THIS WORKS " + leftPremise.conclusion.suc.head + " ==== " +rightPremise.conclusion.ant.tail.tail.head)
//    val v2 = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
//    println(ProofParserSPASS.count + " mgu-C using p._1 " + p._1 +" and p._2 " + p._2)
//    println("RESULTSB: " + v2._1 + " and " + v2._2)
//    //unify((v._1.conclusion.suc.head, v._2.conclusion.ant.tail.tail.head)::Nil)(unifiableVariables)
//    
//     def isUnifiable(p: (E,E)) = unify( p :: Nil)(unifiableVariables) match {
//      case None => false
//      case Some(_) => true
//    }
//    
//    val unifiablePairs = (for (auxL <- v2._1.conclusion.suc; auxR <- v2._2.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)
//    println("ALMOST? " + unifiablePairs.length)
//    }
//
//    if (ProofParserSPASS.count == 26) {
//      println(p)
//      val a = new Var("A",i)
//      val u = new Var("U",i)
//      val v = new Var("V",i)
//      val w = new Var("W",i)
//      val n = new Var("NEW1",i)
//      val aSub = Substitution(v -> a)
//      val nSub = Substitution(n -> v)
//      val uSub = Substitution(u -> w)
//      val vSub = Substitution(a -> u)
//      println("-----> " + vSub(uSub(nSub(aSub(p._1)))))
//      (vSub(uSub(nSub(aSub(p._1)))),p._2)
//    } else {
//    p
//    }
    def cleanNodes = fixSharedNoFilter(leftPremise, rightPremise, 0, unifiableVariables)
    def leftPremiseClean = cleanNodes._1
    def rightPremiseClean = cleanNodes._2
    
    println("leftPremise: " + leftPremise)
    println("leftPremiseClean: " + leftPremiseClean)
    println("rightPremise: " + rightPremise)
    println("rightPremiseClean: " + rightPremiseClean)
    
    def isUnifiable(p: (E,E)) = unify( p :: Nil)(unifiableVariables) match {
      case None => false
      case Some(_) => true
    }
    val unifiablePairs = (for (auxL <- leftPremiseClean.conclusion.suc; auxR <- rightPremiseClean.conclusion.ant) yield (auxL, auxR)).filter(isUnifiable)
    if (unifiablePairs.length > 0) {
      val (auxL, auxR) = unifiablePairs(0)
      new UnifyingResolution(leftPremiseClean, rightPremiseClean, auxL, auxR)
    } else if (unifiablePairs.length == 0) throw new Exception("Resolution: the conclusions of the given premises are not resolvable.")
    else throw new Exception("Resolution: the resolvent is ambiguous.")
  }
  def unapply(p: SequentProofNode) = p match {
    case p: UnifyingResolution => Some((p.leftPremise, p.rightPremise, p.auxL, p.auxR))
    case _ => None
  }
  
  def fixSharedNoFilter(leftPremiseR: SequentProofNode, rightPremiseR: SequentProofNode, count: Int, unifiableVariables: MSet[Var]): (SequentProofNode, SequentProofNode) = {
        
    // For example, suppose we are trying to resolve:

    //  p(X) |- q(a)     with    q(X) |- 

    // note that all variables are assumed to be universally quantified.
    // therefore, the X in the left premise has nothing to do with the X in the right premise.

    //check if there is a variable in both  

    def getSetOfVarsFromPremise(pn: SequentProofNode) = {
   	  val ante = pn.conclusion.ant
   	  val succ = pn.conclusion.suc


      def investigateExpr(e: E): Set[Var] = e match {
        case App(e1, e2) => {
          investigateExpr(e1).union(investigateExpr(e2))
        }
        case Abs(v, e1) => {
          investigateExpr(v).union(investigateExpr(e1))
        }
        case v: Var => {
          //Only care if the variable is a capital         
          val hasLowerCase = v.name.exists(_.isLower)
          val notAnInt = v.name.charAt(0).isLetter
          if (!hasLowerCase && notAnInt) {
            Set[Var](v)
          } else {
            Set[Var]()
          }
        }
      }

      def getSetOfVarsFromExpr(e: Seq[E]): Set[Var] = {
        if (e.length > 1) {
          investigateExpr(e.head).union(getSetOfVarsFromExpr(e.tail))
        } else if (e.length == 1) {
          investigateExpr(e.head)
        } else {
          Set[Var]()
        }
      }
      getSetOfVarsFromExpr(ante).union(getSetOfVarsFromExpr(succ))
    }    
    
    val sharedVars = getSetOfVarsFromPremise(leftPremiseR).intersect(getSetOfVarsFromPremise(rightPremiseR))
        
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

    if (sharedVars.size > 0) {
      //Find, and assign a new name
      //first diff is so that we don't use a variable that is shared
      //second/third diff is so that we don't use a variable appearing in the formula already
      val availableVars = unifiableVariables.diff(sharedVars.union(getSetOfVarsFromPremise(leftPremiseR).union(getSetOfVarsFromPremise(rightPremiseR))))

      var replacement = null.asInstanceOf[Var] //TODO: better way to do this?
      if (availableVars.size >= 1) {
        //use one thats available
        replacement = availableVars.head
      } else {
        replacement = new Var("NEW" + count, i)
        unifiableVariables +=  new Var("NEW" + count, i)
      }
            
      val sub = Substitution(sharedVars.head -> replacement) //perform the replacement
      
      //Substitute the new name into one of the premises; let say the left one //TODO: check: does this matter?
      
      val newAnt = for (a <- leftPremiseR.conclusion.ant) yield sub(a)
      val newSuc = for (a <- leftPremiseR.conclusion.suc) yield sub(a)            
      
      val sA = addAntecedents(newAnt.toList) 
      val sS = addSuccedents(newSuc.toList) 

      val seqOut = sS union sA
      val axOut = Axiom(seqOut)
            
      //TODO: not sure if I can just use a new proof node; this one won't be in the proofMap of the parser. 
      //	Is that going to effect anything? Check.
                 
      fixSharedNoFilter(axOut, rightPremiseR, count + 1, unifiableVariables) //recursively call the function so that any more shared variables are also dealt with
    } else { //sharedVars.size  < 1
      (leftPremiseR, rightPremiseR) //no change
    }
  }  
}
