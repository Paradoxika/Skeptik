package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import at.logic.skeptik.judgment.immutable.{ SetSequent => IClause }
import at.logic.skeptik.expression._
import collection.mutable.{ HashMap => MMap, HashSet => MSet }
import collection.Map
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
import at.logic.skeptik.proof.sequent.resolution.Contraction
import at.logic.skeptik.proof.sequent.resolution.CanRenameVariables
import at.logic.skeptik.proof.sequent.resolution.FindMGU
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.expression.substitution.immutable.Substitution
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents

abstract class FOAbstractRPILUAlgorithm
    extends AbstractRPILUAlgorithm with FindDesiredSequent with CanRenameVariables with FindMGU {

    def getMSet(a: scala.collection.mutable.Set[Var]): MSet[Var] = {
      val out = MSet[Var]()
      for (e <- a) {
        out.add(e)
      }
      out
    }  
  
  protected def checkForRes(safeLiteralsHalf: Set[E], aux: E): Boolean = {

    if (safeLiteralsHalf.size < 1) {
      return false
    }

    /* 
			 * unifiableVars might not contain the variables in the aux formulae. When UR(MRR) generates the auxL/auxR formulae,
			 * it may rename the variables in one premise to a new premise that we just haven't seen yet (and which is resolved out
			 * in that resolution and thus never really visible in the proof, so we need to check for new variables and
			 * add them to our list of unifiable variables or the unification might fail.
			 */

    /*  For example,
			 * 
			 *  p(X) |- q(a)     with    q(X) |- 
			 * 
			 *  UR might rename the right X as Y, then resolve out to get P(X) |-
			 *  And while UR used q(Y) |- and recorded the aux formula as such, it didn't rename
			 *  the right premise, so we never see the variable Y, even though it can be unified.
			 */


    for (safeLit <- safeLiteralsHalf) {
      val uvars = (getSetOfVars(aux) union getSetOfVars(safeLit))
      val uvarsB = getMSet(uvars)
//      val isMore = isMoreGeneral(Sequent(aux)(), Sequent(safeLit)())(uvarsB)//TODO: remove
      unify((aux, safeLit) :: Nil)(getSetOfVars(aux)) match {
        case Some(_) => {
          return true
        }
        case None => {
          //Do nothing
        }
      }
    }
    false
  }

  
protected def checkContracted(old: Sequent, fixed: Sequent): Boolean = {
  var antMissing = false
  for (oldAnt <- old.ant){
    var litFound = false
    for(fixAnt <- fixed.ant){
          val uvars = getMSet(getSetOfVars(oldAnt) union getSetOfVars(fixAnt))
      unify((oldAnt, fixAnt) :: Nil)(uvars) match {
        case Some(_) => {
          litFound = true
        }
        case None => {
          //Do nothing
        }
      }
    }
    if (!litFound){
      antMissing = true
    }
  }
  var sucMissing = false
  for (oldSuc <- old.suc){
    var litFound = false
    for(fixSuc <- fixed.suc){
          val uvars = getMSet(getSetOfVars(oldSuc) union getSetOfVars(fixSuc))
      unify((oldSuc, fixSuc) :: Nil)(uvars) match {
        case Some(_) => {
          litFound = true
        }
        case None => {
          //Do nothing
        }
      }
    }
    if (!litFound){
      sucMissing = true
    }
  }  
  
  return antMissing || sucMissing
  
}
  
protected def checkForResBoth(seq: Sequent, aux: E): Boolean = {

    if (seq.size < 1) {
      return false
    }

    var antContainsAux = false
    if (seq.ant.contains(aux)){
      antContainsAux = true
    } else {
    for (safeLit <- seq.ant) {
      val uvars = getMSet(getSetOfVars(aux) union getSetOfVars(safeLit))
      unify((aux, safeLit) :: Nil)(uvars) match {
        case Some(_) => {
          antContainsAux = true
        }
        case None => {
          //Do nothing
        }
      }
    }
    }
    
    var sucContainsAux = false
    if (seq.suc.contains(aux)){
      sucContainsAux = true
    } else {
    for (safeLit <- seq.suc) {
      val uvars = getMSet(getSetOfVars(aux) union getSetOfVars(safeLit))
      unify((aux, safeLit) :: Nil)(uvars) match {
        case Some(_) => {
          sucContainsAux = true
        }
        case None => {
          //Do nothing
        }
      }
    }
    }
    
    return sucContainsAux && antContainsAux
  }  
  
  //(jgorzny) 2 June 2015:
  //This checks the aux after the original mgu was applied
  //prevents some terrible attempts to lower
  //NOTE: p MUST be a unifying resolution node
  protected def checkForResSmart(safeLiteralsHalf: Set[E], aux: E, p: SequentProofNode): Boolean = {

    if (safeLiteralsHalf.size < 1) {
      return false
    }

    /* 
			 * unifiableVars might not contain the variables in the aux formulae. When UR(MRR) generates the auxL/auxR formulae,
			 * it may rename the variables in one premise to a new premise that we just haven't seen yet (and which is resolved out
			 * in that resolution and thus never really visible in the proof, so we need to check for new variables and
			 * add them to our list of unifiable variables or the unification might fail.
			 */

    /*  For example,
			 * 
			 *  p(X) |- q(a)     with    q(X) |- 
			 * 
			 *  UR might rename the right X as Y, then resolve out to get P(X) |-
			 *  And while UR used q(Y) |- and recorded the aux formula as such, it didn't rename
			 *  the right premise, so we never see the variable Y, even though it can be unified.
			 */



    def oldMGU = p.asInstanceOf[UnifyingResolution].mgu
    def newAux = oldMGU(aux)
//    println("newAux: " + newAux)
    for (safeLit <- safeLiteralsHalf) {
      val uvars = (getSetOfVars(newAux) union getSetOfVars(safeLit))
      val uvarsB = getMSet(uvars)
//      val isMore = isMoreGeneral(Sequent(newAux)(), Sequent(safeLit)())(uvarsB)//not used //TODO: remove
//      unify((newAux, safeLit) :: Nil)(getSetOfVars(newAux)) match {
      
      unify((newAux, safeLit) :: Nil)(getSetOfVars(newAux)) match {
        case Some(_) => {
          return true
        }
        case None => {
          //Do nothing
        }
      }
    }
    false
  }

  class FOEdgesToDelete extends EdgesToDelete {

    override def nodeIsMarked(node: SequentProofNode): Boolean = {
      // may be optimized (edgesToDelete contains node is checked 3 times)
      node match {
        case _ if ((edges contains node) && edges(node)._2) => true
        case UnifyingResolution(left, right, _, _) if (isMarked(node, left) && isMarked(node, right)) =>
          deleteNode(node)
          true
        case _ => false
      }
    }

    override protected def sideOf(parent: SequentProofNode, child: SequentProofNode) = child match {
      case UnifyingResolution(left, right, _, _) => if (parent == left) LeftDS
      else if (parent == right) RightDS
      else throw new Exception("Unable to find parent in child")
      case _ => throw new Exception("This function should never be called with child not being a UR")
    }

  }

  protected def isMRRContraction(c: Contraction): Boolean = {
    if (c.premises.size == 1) {
      c.premises.head match {
        case UnifyingResolutionMRR(_, _, _, _) => return true
        case _                                 => return false
      }
    }
    false
  }
//TODO: refactor (this is a copy)
  protected def finalCheck(safeLit: Sequent, seqToDelete: Sequent, allowSubset: Boolean): Boolean = {

    def desiredIsContained(safe: Sequent, toDelete: Sequent): Boolean = {
      if (checkIfConclusionsAreEqual(safe, toDelete)) {
        return true
      } else if (toDelete.ant.toSet.subsetOf(safe.ant.toSet) && toDelete.suc.toSet.subsetOf(safe.suc.toSet)) {
        return true
      } else {
        val cVars = getSetOfVars(toDelete.ant: _*) union getSetOfVars(toDelete.suc: _*)

        val (mapIsUniquelyValid, intersectedMap) = computeIntersectedMap(safe, toDelete, cVars,allowSubset) //Aug11

        if (mapIsUniquelyValid) {
          if (!checkMapSub(intersectedMap, cVars, toDelete, safe)) {
            return false
          } else {
            return true
          }
        } else {
          return checkInvalidMap(intersectedMap, cVars, toDelete, safe, true)

        }
      }
    }

    def antVars = getSetOfVars(seqToDelete.ant: _*)
    def sucVars = getSetOfVars(seqToDelete.suc: _*)
    def antVarsB = getSetOfVars(safeLit.ant: _*)
    def sucVarsB = getSetOfVars(safeLit.suc: _*)
    def allvars = MSet[Var]() ++ antVars ++ sucVars ++ antVarsB ++ sucVarsB
    def safeClean = fixSharedNoFilter(Axiom(safeLit), Axiom(seqToDelete), 0, allvars)
    def vars = MSet[Var]() ++ antVars ++ sucVars

    desiredIsContained(safeClean.conclusion, seqToDelete)

  }
  
  
  // Main functions
  protected def fixProofNodes(edgesToDelete: EdgesToDelete, unifiableVariables: MSet[Var], auxMap: MMap[SequentProofNode, E], mguMap: MMap[SequentProofNode, Substitution], done: MSet[String])(p: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
    lazy val fixedLeft = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;

    var resMap = new MMap[SequentProofNode, MSet[Substitution]]()
    p match {
      //      case Axiom(conclusion) => p

      //      case FOSubstitution(prem,_) => {
      //        p
      //      }

      case Contraction(_, _) if isMRRContraction(p.asInstanceOf[Contraction]) => {
        println("About to contract.")
        println("fixedleft:  " + fixedLeft)
        println("fixedRight: " + fixedRight)
        println(" old:       " + p.conclusion)
        try {
          val out = Contraction(fixedLeft, p.conclusion)(unifiableVariables)
          println(" new:       " + out.conclusion)
          p //if we can find the old conclusion from the fixed node, it's the same. memory optimization
        } catch {
          case t: Throwable => {
            val con = contractIfHelpful(fixedLeft)(unifiableVariables)
            println("CON : " + con )
            println(finalCheck(con.conclusion, p.conclusion, true) + " " + finalCheck(p.conclusion, con.conclusion, true))
            println(checkSubsetOrEquality(true, p.conclusion, con.conclusion) + " " + checkSubsetOrEquality(true, con.conclusion, p.conclusion))
//            if (!checkSubsetOrEquality(true, p.conclusion, con.conclusion) && (p.conclusion.ant.size != 0 || p.conclusion.suc.size != 0)) {
////              println("CON-con")
////              if(finalCheck(con.conclusion, p.conclusion)){
////                fixedLeft //con
////              } else {
////                p
////              }
////              con
//              fixedLeft
//            } else {
//              p
//            }
            //4:40
//            if(finalCheck(con.conclusion, p.conclusion, true) || finalCheck(p.conclusion, con.conclusion, true)){ 
//            if(!finalCheck(fixedLeft.conclusion, p.conclusion, true)){
            
//            if(!finalCheck(p.conclusion, fixedLeft.conclusion, true) && !checkSubsetOrEquality(true, p.conclusion, con.conclusion)){//12:08 TODO            
            if(!checkContracted(p.conclusion, fixedLeft.conclusion)){//11:50am
              println("using FL (con): "+ fixedLeft)
              fixedLeft
            } else {
              p
            }
          }
        }
        //        contractIfHelpful(fixedLeft)(unifiableVariables)
      }

      // If we've got a proof of false, we propagate it down the proof
      case UnifyingResolution(_, _, _, _) if (fixedLeft.conclusion.ant.isEmpty) && (fixedLeft.conclusion.suc.isEmpty) => {
//        println("URmatch, using FL")
        fixedLeft
      }

      case UnifyingResolution(_, _, _, _) if (fixedRight.conclusion.ant.isEmpty) && (fixedRight.conclusion.suc.isEmpty) => {
//        println("URmatch, using FR ")
        fixedRight
        
      }

      // Delete nodes and edges
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, left) => {
        val sub = p.asInstanceOf[UnifyingResolution].mgu
        mguMap.put(fixedRight, sub)
//                println("URmatchb, using FR " + fixedRight)

        fixedRight
//        contractIfHelpful(fixedRight)(unifiableVariables)
      }
      case UnifyingResolution(left, right, _, _) if edgesToDelete.isMarked(p, right) => {
        val sub = p.asInstanceOf[UnifyingResolution].mgu
        mguMap.put(fixedLeft, sub)
//                println("URmatchb, using Fl " + fixedLeft)

        fixedLeft
//        contractIfHelpful(fixedLeft)(unifiableVariables)
        
      }

      // If premises haven't been changed, we keep the proof as is (memory optimization)
      case UnifyingResolution(left, right, _, _) if (left eq fixedLeft) && (right eq fixedRight) => {
//        println("urmatch p " + p.conclusion)
        //10:25 all of this (used to return p)
        try {
          val lDistinct = Sequent(fixedLeft.conclusion.ant.distinct: _*)(fixedLeft.conclusion.suc.distinct: _*)
          val newL = Contraction(fixedLeft, lDistinct)(unifiableVariables)
          
          val rDistinct = Sequent(fixedRight.conclusion.ant.distinct: _*)(fixedRight.conclusion.suc.distinct: _*)
          val newR = Contraction(fixedRight, rDistinct)(unifiableVariables)
          
          if (checkIfConclusionsAreEqual(newR, fixedRight) && checkIfConclusionsAreEqual(newL, fixedLeft)){
            return p
          }
          
          println("MARKING DONE: " + p.conclusion.toString)
            done.add(p.conclusion.toString)
            val k = UnifyingResolutionMRR(newL, newR)(unifiableVariables)
//            val k = try {
//              UnifyingResolutionMRR(newL, newR, p.conclusion)(unifiableVariables)
//            } catch {
//              case h: Exception => {
//                 UnifyingResolutionMRR(newL, newR)(unifiableVariables)
//              }
//            }
//          println("k,p: " + k.conclusion)
//          println("     " + p.conclusion)
//          println(fixedLeft)
//          println(newL)
//          println(fixedRight)
//          println(newR)
              k
        }catch {
          case a: Throwable => {
            println("urmatch p failed!")
            p
          }
        }
//                try {
//
//          val newS = Sequent(p.conclusion.ant.distinct:_*)(p.conclusion.suc.distinct:_*)
//          done.add(p.conclusion.toString)
//          UnifyingResolutionMRR(fixedLeft, fixedRight, newS)(unifiableVariables)
//          
//        }catch {
//          case a: Throwable => {
//            println("urmatch p failed!")
//            p
//          }
//        }
//        done.add(p.conclusion.toString)
//        contractIfHelpful(p)(unifiableVariables)
//      p
      }

      case UnifyingResolution(left, right, pivot, _) if (findRenaming(fixedLeft.conclusion, p.conclusion)(unifiableVariables) != null) => {
        //If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
        //the fixed parent; so the pivot better be missing.
        assert(!checkForRes(fixedLeft.conclusion.toSetSequent.suc, pivot))
//                println("URmatchc, using Fl " + fixedLeft)

        fixedLeft
//        contractIfHelpful(fixedLeft)(unifiableVariables)
      }
      case UnifyingResolution(left, right, _, pivot) if (findRenaming(fixedRight.conclusion, p.conclusion)(unifiableVariables) != null) => {
        //If we're doing this, its because the fixed parent doesn't contain the pivot, so we replace it with 
        //the fixed parent; so the pivot better be missing.
        assert(!checkForRes(fixedLeft.conclusion.toSetSequent.ant, pivot))
//                println("URmatchc, using FR " + fixedRight)

        fixedRight
//        contractIfHelpful(fixedRight)(unifiableVariables)
      }

      // Main case (rebuild a resolution)
      case UnifyingResolution(left, right, auxL, auxR) => {
//println("ur-main: " + p.conclusion)
//println(done.contains(p.conclusion.toString))
//if(done.contains(p.conclusion.toString)){
//  p
//}

        val nonEmptyLeftMap = !auxMap.get(left).isEmpty && !mguMap.get(left).isEmpty
        val nonEmptyRightMap = !auxMap.get(right).isEmpty && !mguMap.get(right).isEmpty

        val ambiguousErrorStringMRR = "Resolution (MRR): the resolvent is ambiguous."
        val ambiguousErrorString = "Resolution: the resolvent is ambiguous."

        //We may have to apply a FO sub
        def newFixedRight = if (!mguMap.get(fixedRight).isEmpty) {
          makeFOSub(fixedRight, mguMap.get(fixedRight).get)(unifiableVariables)
        } else {
          fixedRight
        }

        def newFixedLeft = if (!mguMap.get(fixedLeft).isEmpty) {
          makeFOSub(fixedLeft, mguMap.get(fixedLeft).get)(unifiableVariables)
        } else {
          fixedLeft
        }

        val out = try {
          //          UnifyingResolutionMRR(newFixedRight, fixedLeft)(unifiableVariables)

          //-----26 Nov 2016
          if (checkIfConclusionsAreEqual(newFixedRight, fixedLeft)) {
            val rProofSize = Proof[SequentProofNode](newFixedRight).size
            val lProofSize = Proof[SequentProofNode](fixedLeft).size
            if (rProofSize > lProofSize) {
              fixedLeft
            } else {
              newFixedRight
            }
          } else {
            
//            val res = try {
//              UnifyingResolutionMRR(newFixedRight, fixedLeft, p.conclusion)(unifiableVariables)
//              
//            } catch {
//              case aa: Throwable =>{
//                try {
//                  UnifyingResolutionMRR(fixedLeft, newFixedRight, p.conclusion)(unifiableVariables)
//                } catch {
//                  case ab: Throwable => {
//                    UnifyingResolutionMRR(newFixedRight, fixedLeft)(unifiableVariables)
//                  }
//                }
//              }
//            }
            
//            val res = if (fixedLeft.conclusion.suc.toSeq.contains(auxL)){
//              println("order changed!")
//              UnifyingResolution(fixedLeft, newFixedRight, p.conclusion)(unifiableVariables)
//            } else {
//              println("order stayed")
//              UnifyingResolution(newFixedRight, fixedLeft)(unifiableVariables)
//            }
            
            
//              val res =try { 
// UnifyingResolutionMRR(fixedLeft, newFixedRight, p.conclusion)(unifiableVariables)//10:25 changed order (and in the corresponding one below)                              
//              } catch {
//                case aaaa: Exception =>{
//UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables)//10:25 changed order (and in the corresponding one below)                  
//                }
//              }
//              
              val res = UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables)//10:25 changed order (and in the corresponding one below)
              
              
              
//            val res = UnifyingResolutionMRR(newFixedRight, fixedLeft)(unifiableVariables)
//            val res = UnifyingResolutionMRR(contractIfHelpful(newFixedRight)(unifiableVariables), contractIfHelpful(fixedLeft)(unifiableVariables))(unifiableVariables)
            
//            println("RES: " + res)
//            println("--L: " + fixedLeft)
//            println("--R: " + newFixedRight)
//            println("--p: " + p.conclusion)
            res
          }
          //-----26 Nov 2016 ends

        } catch {
          case e: Exception => {
            if (e.getMessage() != null && e.getMessage.equals(ambiguousErrorString)) {
              if (nonEmptyLeftMap && !nonEmptyRightMap) {
                val oldMGU = mguMap.get(left).get
                fixAmbiguous(fixedLeft, newFixedRight, oldMGU, left, right, auxL, auxR, p.conclusion)(unifiableVariables)
              } else {
                val oldMGU = mguMap.get(right).get
                fixAmbiguous(newFixedLeft, fixedRight, oldMGU, left, right, auxL, auxR, p.conclusion)(unifiableVariables)
              }
            } else {
//              println("*"); e.printStackTrace();
//              println(fixedLeft)
//              println(fixedRight)
//              println(newFixedRight)
//
//              println("*")
              //                            attemptGreedyContraction(fixedLeft, fixedRight, newFixedRight, ambiguousErrorString, ambiguousErrorStringMRR, left, right, auxL, auxR, mguMap, p.conclusion)(unifiableVariables)
              //                             attemptGreedyContraction(contractIfHelpful(fixedLeft)(unifiableVariables), contractIfHelpful(fixedRight)(unifiableVariables), contractIfHelpful(newFixedRight)(unifiableVariables), ambiguousErrorString, ambiguousErrorStringMRR, left, right, auxL, auxR, mguMap, p.conclusion)(unifiableVariables)
              try {
//                                val a = UnifyingResolution(fixedLeft, newFixedRight)(unifiableVariables) 

                val a = UnifyingResolution(newFixedRight, fixedLeft)(unifiableVariables) //3:50pm//10:20
//                val a = UnifyingResolutionMRR(contractIfHelpful(fixedLeft)(unifiableVariables), contractIfHelpful(newFixedRight)(unifiableVariables))(unifiableVariables)
                println("returning(a) " + a)
                a
              } catch {
                case f: Exception => {
                  val a = attemptGreedyContraction(contractIfHelpful(fixedLeft)(unifiableVariables), fixedRight,
                    newFixedRight, ambiguousErrorString, ambiguousErrorStringMRR, left, right, auxL, auxR, mguMap, p.conclusion)(unifiableVariables)
                  println("returning " + a)
                  a
                }
              }
            }
          }
        }

        out
      }

      // When the inference is not UR, nothing is done 
      case _ => {
        p
      }
    }
  }

  def attemptGreedyContraction(fixedLeft: SequentProofNode, fixedRight: SequentProofNode, newFixedRight: SequentProofNode,
                               ambiguousErrorString: String, ambiguousErrorStringMRR: String, left: SequentProofNode, right: SequentProofNode, auxL: E, auxR: E,
                               mguMap: MMap[SequentProofNode, Substitution], oldConclusion: Sequent)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    
//    println("l: " + left)
//    println("r: " + right)
//    println("FR: " + fixedRight)
//    println("FL: " + fixedLeft)
//    println("NFR: " + newFixedRight)
//    println("oc: " + oldConclusion)
    try {
      UnifyingResolution(fixedLeft, newFixedRight)(unifiableVariables)
    } catch {
      case e: Exception if (e.getMessage() != null && (e.getMessage.contains(ambiguousErrorString) || e.getMessage.contains(ambiguousErrorStringMRR))) => {
        println("ambig found, correctly.")
        try {
          //9:50, added this
          if (checkIfConclusionsAreEqual(contractIfHelpful(fixedLeft)(unifiableVariables), left) && checkIfConclusionsAreEqual(contractIfHelpful(fixedRight)(unifiableVariables), right)) {
            //If the fixed are the same as the old, nothing is changed in this part. Use the old conclusion as a goal
            //to fix the amibuigity; greedy contraction risks the proof failing to end with the empty sequent.
            val success = UnifyingResolution(contractIfHelpful(fixedLeft)(unifiableVariables), contractIfHelpful(fixedRight)(unifiableVariables), oldConclusion)(unifiableVariables)//9:50 changed to no MRR
            println("returning correctly? " + success)
            return success
          }          
          if (checkIfConclusionsAreEqual(fixedLeft, left) && checkIfConclusionsAreEqual(fixedRight, right)) {
            //If the fixed are the same as the old, nothing is changed in this part. Use the old conclusion as a goal
            //to fix the amibuigity; greedy contraction risks the proof failing to end with the empty sequent.
            val success = UnifyingResolution(fixedLeft, fixedRight, oldConclusion)(unifiableVariables)//9:50 changed to no MRR
            println("returning correctl?b " + success)
            return success
          }
        } catch {
          case h: Exception => {
            //do nothing 
          }
        }
        try {
//          UnifyingResolutionMRR(fixedLeft, Contraction(fixedRight)(unifiableVariables))(unifiableVariables)
          val k =UnifyingResolutionMRR(fixedLeft, contractIfHelpful(fixedRight)(unifiableVariables))(unifiableVariables) //9:00pm
          println("ur-k" + k)
          k
        } catch {
          case f: Exception => {

            val oldMGU = if (!mguMap.get(left).isEmpty) {
              mguMap.get(left).get
            } else {
              null
            }
            fixAmbiguous(fixedLeft, fixedRight, oldMGU, left, right, auxL, auxR, oldConclusion)(unifiableVariables)
          }
        }

      }
      case e: Exception => {
        val oldConclusionIsNotEmpty = !(oldConclusion.ant.size == 0 && oldConclusion.suc.size == 0) //1:30
        if (checkIfConclusionsAreEqual(fixedRight, fixedLeft)) {
          fixedRight
        } else if (checkSubsetOrEquality(true, fixedRight.conclusion, oldConclusion)) {
          println("caseA")
          fixedRight
        } else if (checkSubsetOrEquality(true, fixedLeft.conclusion, oldConclusion)) {
          println("caseB")
          fixedLeft

//                    //1:30am change: these two 
//                  } else if (checkSubsetOrEquality(true, oldConclusion, fixedRight.conclusion) && oldConclusionIsNotEmpty) {
//                    println("C")
//                    fixedRight          
//                  } else if (checkSubsetOrEquality(true, oldConclusion, fixedLeft.conclusion) && oldConclusionIsNotEmpty) {
//                    println("D")
//                    fixedLeft           

        } else {

          try {
            //            println("l: " + left)
            //            println("r: " + right)
            //            println("FR: " + fixedRight)
            //            println("FL: " + fixedLeft)
            //            println("NFR: " + newFixedRight)
            //            println("oc: " + oldConclusion)

            val out =
              if (contractFixedFindsTarget(fixedLeft, oldConclusion) != null) {
                val t = contractFixedFindsTarget(fixedLeft, oldConclusion)
                println("using CON: " + t)
                t
              } else if (contractFixedFindsTarget(fixedRight, oldConclusion) != null) {
                val t = contractFixedFindsTarget(fixedRight, oldConclusion)
                println("using CON: " + t)
                t
              } else if (checkIfConclusionsAreEqual(fixedLeft, left)) {
//                              if (checkIfConclusionsAreEqual(fixedLeft, left)) {
                println("using FR")
                fixedRight
              } else if (checkIfConclusionsAreEqual(fixedRight, right)) {
                println("using FL")
                fixedLeft
              } else {
                println("going to try MRR.")
                println(newFixedRight)
                println(fixedLeft)
                try {
                  UnifyingResolutionMRR(newFixedRight, fixedLeft)(unifiableVariables)
                } catch {
                  case g: Exception => {
                    g.printStackTrace()
                    UnifyingResolutionMRR(fixedLeft, newFixedRight)(unifiableVariables)
                  }
                }
              }
            println("long checks: " + out)
            out
          } catch {
            case f: Exception => {
              f.printStackTrace()
//              throw new Exception("FORPI Failed!")
              fixedRight
            }
          }

        }
      }
    }
  }

  def contractFixedFindsTarget(premise: SequentProofNode, seq: Sequent)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    try {
//      println("checking equal..??? " + seq + " and " + premise.conclusion)
      if(checkIfConclusionsAreEqual(premise.conclusion, seq)){
        premise
      } else {
        if(seq.ant.size != 0 || seq.suc.size != 0){
        val out = Contraction(premise, seq)(unifiableVariables)
       println("out??? " + out + " and " + premise.conclusion)
        out
        } else {
          premise
        }
      }
    } catch {
      case _: Throwable => {
        null
      }
    }
  }

  def makeFOSub(premise: SequentProofNode, sub: Substitution)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    val FOSub = new FOSubstitution(premise, sub)
    if (checkIfConclusionsAreEqual(FOSub, premise)) {
      premise
    } else {
      FOSub
    }
  }

  def tryGreedyContraction(left: SequentProofNode, right: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    try {
      val quickFix = UnifyingResolution(Contraction(left), right)
      println("quickFix " + quickFix)
      return quickFix
    } catch {
      case _: Throwable => { //do nothing
      }
    }

    val quickFixReverse = UnifyingResolution(left, Contraction(right))
      println("quickFixReverse " + quickFixReverse)
    
    return quickFixReverse

  }

  def fixAmbiguous(fLeft: SequentProofNode, fRight: SequentProofNode, oldMGU: Substitution, left: SequentProofNode, right: SequentProofNode,
                   auxL: E, auxR: E, oldConclusion: Sequent)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {

    println("FA entered")
    try {
      val quickFix = tryGreedyContraction(fLeft, fRight)
      return quickFix
    } catch {
      case _: Throwable => { //do nothing - we have work to do.
      }
    }

    val newMGU = unify((auxL, auxR) :: Nil).get //should always be non-empty

    val mgu = if (oldMGU != null) {
      oldMGU
    } else {
      Substitution()
    }

    val leftEq = findRenaming(fLeft, left) != null
    val rightEq = findRenaming(fLeft, left) != null

    val fLeftClean = if (!fLeft.equals(left)) {
      makeFOSub(fLeft, mgu).conclusion
    } else {
      fLeft.conclusion
    }
    val (leftRemainder, leftSub) = findRemainder(fLeftClean, auxL, mgu, leftEq, true)

    val fRightClean = if (!fRight.equals(right)) {
      makeFOSub(fRight, mgu).conclusion
    } else {
      fRight.conclusion
    }
    val (rightRemainder, rightSub) = findRemainder(fRightClean, auxR, mgu, rightEq, false)

    val rightRemainderWithNewMGU = makeFOSub(Axiom(rightRemainder), newMGU).conclusion

    val tempLeft = makeFOSub(makeFOSub(Axiom(leftRemainder), leftSub), newMGU)

    val tempRight = Axiom(rightRemainderWithNewMGU)
    val cleanLeftRemainder = fixSharedNoFilter(tempLeft, tempRight, 0, unifiableVariables).conclusion

    val newTarget = rightRemainderWithNewMGU.union(tempLeft.conclusion)

    val finalLeft = useFOSubIfEqual(leftEq, fLeft, mgu)
    val finalRight = useFOSubIfEqual(rightEq, fRight, mgu)

    val newFinalRight = findTargetIfEqual(rightEq, right, finalRight)
    val newFinalLeft = findTargetIfEqual(leftEq, left, finalLeft)

    val out = try {
      UnifyingResolution(newFinalLeft, newFinalRight, oldConclusion) //28 Oct 
    } catch {
      case e: Exception => {
        if (e.getMessage.contains("Cannot find desired resolvent")) {
          UnifyingResolution(contractIfHelpful(newFinalLeft), contractIfHelpful(newFinalRight), contractIfHelpful(Axiom(oldConclusion)).conclusion)
        } else {
          UnifyingResolution(finalRight, finalLeft)
        }
      }
    }
    println("fixAmbig returning" + out) 
    out
  }

  def useFOSubIfEqual(equal: Boolean, premise: SequentProofNode,
                      sub: Substitution)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    if (equal) {
      return makeFOSub(premise, sub)
    } else {
      premise
    }
  }

  def findTargetIfEqual(equal: Boolean, oldPremise: SequentProofNode,
                        newPremise: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    if (equal) {
      try {
        findTarget(oldPremise, newPremise)
      } catch {
        case _: Throwable => {
          newPremise
        }
      }
    } else {
      newPremise
    }
  }

  def findTarget(original: SequentProofNode, fixed: SequentProofNode)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    return Contraction(fixed, original.conclusion)

  }

  def findRemainder(seq: Sequent, target: E, mgu: Substitution, applySub: Boolean, removeFromAnt: Boolean)(implicit unifiableVariables: MSet[Var]): (Sequent, Substitution) = {
    val (newAnt, antSub) = if (removeFromAnt) { checkHalf(seq.ant, target, mgu, applySub) } else { (seq.ant.toList, null) }
    val (newSuc, sucSub) = if (!removeFromAnt) { checkHalf(seq.suc, target, mgu, applySub) } else { (seq.suc.toList, null) }

    val subOut = if (antSub != null) { antSub } else { sucSub } //at least one of these must be non-empty
    //both should never be empty

    val out = addAntecedents(newAnt) union addSuccedents(newSuc)
    (out, subOut)
  }

  def areAlphaEq(a: E, b: E)(implicit unifiableVariables: MSet[Var]): Boolean = {
    findRenaming(Sequent(a)(), Sequent(b)()) != null
  }

  //TODO: should this be removed?
  def checkHalf(half: Seq[E], target: E, sub: Substitution, applySub: Boolean)(implicit unifiableVariables: MSet[Var]): (List[E], Substitution) = {
    def filterHelper(e: E): Boolean = {
      areAlphaEq(sub(e), target)
    }

    val newSeq = if (applySub) {
      half.filter(!filterHelper(_))
    } else {
      half.filter(!areAlphaEq(_, target))
    }

    val diffs = half.diff(newSeq)

    val subOut = if (diffs.size > 0) {
      val formula = diffs.head //should only be one

      val renameSub = unify((formula, target) :: Nil)
      renameSub.get //should never be empty
    } else {
      null
    }

    (newSeq.toList, subOut)
  }

}

abstract class FOAbstractRPIAlgorithm
    extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  def findActualAux(seqHalf: Seq[E], aux: E, mgu: Substitution): E = {
    for (s <- seqHalf) {
      if (mgu(s).equals(aux)) {
        return s
      }
    }
    aux
  }

  protected def safeLiteralsFromChild(childWithSafeLiterals: (SequentProofNode, IClause),
                                      parent: SequentProofNode, edgesToDelete: FOEdgesToDelete) = {

    childWithSafeLiterals match {
      //in these cases, 'child' is the unifying resolution
      case (child @ UnifyingResolution(left, right, _, auxR), safeLiterals) if left == parent =>
        if (edgesToDelete.isMarked(child, right)) {
          safeLiterals
        } else {
          def auxRb = findActualAux(left.conclusion.suc, auxR, child.asInstanceOf[UnifyingResolution].mgu)
//          println("adding " + auxRb + " as safe for " + childWithSafeLiterals._1)
          addLiteralSmart(safeLiterals, auxRb, false, left, right)
        }

      case (child @ UnifyingResolution(left, right, auxL, _), safeLiterals) if right == parent =>
        if (edgesToDelete.isMarked(child, left)) {
          safeLiterals
        } else {
          def auxLb = findActualAux(right.conclusion.ant, auxL, child.asInstanceOf[UnifyingResolution].mgu)
//          println("adding " + auxL + " as safe for " + childWithSafeLiterals._1)
          //          println("diff: " + auxL + " and ")
          //          println("      " + auxLb)
          addLiteralSmart(safeLiterals, auxL, true, left, right) //TODO: should this be auxLb?
        }

      case (p, safeLiterals) => {
        safeLiterals
      }
    }
  }

  protected def addLiteralSmart(seq: IClause, aux: E, addToAntecedent: Boolean, left: SequentProofNode, right: SequentProofNode): IClause = {
    //Restrict MartelliMontanari to tell whether "aux" is more general (and not just unifiable) 
    // by passing only the variables of "aux" as unifiable variables.
    val uVars = new MSet[Var]() union getSetOfVars(aux)
    val seqHalf = if (addToAntecedent) {
      seq.ant
    } else {
      seq.suc
    }

    for (lit <- seqHalf) {
      unify((lit, aux) :: Nil)(uVars) match {
        case None => {}
        case Some(_) => {
          return seq
        }
      }
    }
    def out = if (addToAntecedent) {
      (aux +: seq)
    } else {
      (seq + aux)
    }
    out
  }

  protected def computeSafeLiterals(proof: SequentProofNode,
                                    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
                                    edgesToDelete: FOEdgesToDelete): IClause

}

trait FOCollectEdgesUsingSafeLiterals
    extends FOAbstractRPIAlgorithm with FindDesiredSequent {

  //ensure that the node that will be replacing the unifying resolution is entirely safe
//  protected def finalCheck(safeLit: Sequent, seqToDelete: Sequent): Boolean = {
//
//    def desiredIsContained(safe: Sequent, toDelete: Sequent): Boolean = {
//      if (checkIfConclusionsAreEqual(safe, toDelete)) {
//        return true
//      } else if (toDelete.ant.toSet.subsetOf(safe.ant.toSet) && toDelete.suc.toSet.subsetOf(safe.suc.toSet)) {
//        return true
//      } else {
//        val cVars = getSetOfVars(toDelete.ant: _*) union getSetOfVars(toDelete.suc: _*)
//
//        val (mapIsUniquelyValid, intersectedMap) = computeIntersectedMap(safe, toDelete, cVars) //Aug11
//
//        if (mapIsUniquelyValid) {
//          if (!checkMapSub(intersectedMap, cVars, toDelete, safe)) {
//            return false
//          } else {
//            return true
//          }
//        } else {
//          return checkInvalidMap(intersectedMap, cVars, toDelete, safe, true)
//
//        }
//      }
//    }
//
//    def antVars = getSetOfVars(seqToDelete.ant: _*)
//    def sucVars = getSetOfVars(seqToDelete.suc: _*)
//    def antVarsB = getSetOfVars(safeLit.ant: _*)
//    def sucVarsB = getSetOfVars(safeLit.suc: _*)
//    def allvars = MSet[Var]() ++ antVars ++ sucVars ++ antVarsB ++ sucVarsB
//    def safeClean = fixSharedNoFilter(Axiom(safeLit), Axiom(seqToDelete), 0, allvars)
//    def vars = MSet[Var]() ++ antVars ++ sucVars
//
//    desiredIsContained(safeClean.conclusion, seqToDelete)
//
//  }

  protected def collectEdgesToDelete(nodeCollection: Proof[SequentProofNode]) = {
    val edgesToDelete = new FOEdgesToDelete()
    var auxMap = new MMap[SequentProofNode, E]()
    var mguMap = new MMap[SequentProofNode, Substitution]()
    def visit(p: SequentProofNode, childrensSafeLiterals: Seq[(SequentProofNode, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
//      println(safeLiterals + " are safe for " + p)
//      if(p.isInstanceOf[UnifyingResolution]){
//          p match {
//            case UnifyingResolution(left, right, auxL, auxR) => {
//            val whatA = checkForRes(safeLiterals.ant, auxL) 
//            val whatB =  checkForResSmart(safeLiterals.ant, auxL, p)
//            val whatC = checkForRes(safeLiterals.suc, auxL)
//            val whatD = checkForResSmart(safeLiterals.suc, auxL, p)
//            println(p)
//            println("L: " + auxL + " and R: " + auxR)
//            println(whatA + " " + whatB + " " + whatC + " " + whatD)
//            
//            }
//          }
//          
//      }
      p match {

        case UnifyingResolution(left, right, auxL, auxR) if (
          (checkForRes(safeLiterals.ant, auxR) && checkForResSmart(safeLiterals.ant, auxR, p)
          && checkForRes(safeLiterals.suc, auxL) && checkForResSmart(safeLiterals.suc, auxL, p))
          || checkForResBoth(safeLiterals.toSeqSequent, auxL)) => { //11:50 change
          //if the pivot appears in both the antecedent and succedent of the safe literals, we don't know
          //which edge to mark. Better not touch either.
          println("BOTH : " + p)
        }
          
        case UnifyingResolution(left, right, auxL, auxR) if (
          checkForRes(safeLiterals.ant, auxR) && checkForResSmart(safeLiterals.ant, auxR, p)
          && checkForRes(safeLiterals.suc, auxR) && checkForResSmart(safeLiterals.suc, auxR, p)) => {
          //if the pivot appears in both the antecedent and succedent of the safe literals, we don't know
          //which edge to mark. Better not touch either.
          println("BOTHa : " + p)
        }  
          
        case UnifyingResolution(left, right, auxL, auxR) if (
          checkForRes(safeLiterals.ant, auxL) && checkForResSmart(safeLiterals.ant, auxL, p)
          && checkForRes(safeLiterals.suc, auxL) && checkForResSmart(safeLiterals.suc, auxL, p)) => {
          //if the pivot appears in both the antecedent and succedent of the safe literals, we don't know
          //which edge to mark. Better not touch either.
          println("BOTHb : " + p)
        }          

        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.suc, auxL)
          && checkForResSmart(safeLiterals.suc, auxL, p) && finalCheck(safeLiterals.toSeqSequent, left.conclusion, false)) => {
          auxMap.put(p, auxL)
          mguMap.put(p, p.asInstanceOf[UnifyingResolution].mgu)
          println("marking edge between " + p + " and " + right + " auxL: " + auxL)
          println("A: " + (checkForRes(safeLiterals.suc, auxL) && checkForResSmart(safeLiterals.suc, auxL, p)))
          println("so " + left + " should be in safe: " + safeLiterals)
          edgesToDelete.markRightEdge(p)
        }
        case UnifyingResolution(left, right, auxL, auxR) if (checkForRes(safeLiterals.ant, auxR) &&
          checkForResSmart(safeLiterals.ant, auxR, p) && finalCheck(safeLiterals.toSeqSequent, right.conclusion, false)) => {
          auxMap.put(p, auxR)
          mguMap.put(p, p.asInstanceOf[UnifyingResolution].mgu)
          println("marking edge between " + p + " and " + left + " auxR: " + auxR)
          println("B: " + (checkForRes(safeLiterals.ant, auxR) && checkForResSmart(safeLiterals.ant, auxR, p)))
          println("so " + right + " should be in safe: " + safeLiterals)

          edgesToDelete.markLeftEdge(p)
        }
        case _ =>
      }
      (p, safeLiterals)
    }
    nodeCollection.bottomUp(visit)
    (edgesToDelete, auxMap, mguMap)
  }
}

trait FOUnitsCollectingBeforeFixing
    extends FOAbstractRPILUAlgorithm with CanRenameVariables {

  protected def getAllVars(proof: Proof[SequentProofNode]): MSet[Var] = {
    val out = MSet[Var]()
    for (n <- proof) {
      val vars = getSetOfVars(n)
      for (v <- vars) {
        out += v
      }
    }
    out
  }
}

trait FOIntersection
    extends FOAbstractRPIAlgorithm {

  protected def computeSafeLiterals(proof: SequentProofNode,
                                    childrensSafeLiterals: Seq[(SequentProofNode, IClause)],
                                    edgesToDelete: FOEdgesToDelete): IClause = {
    childrensSafeLiterals.filter { x => !edgesToDelete.isMarked(x._1, proof) } match {
      case Nil =>
        if (!childrensSafeLiterals.isEmpty) edgesToDelete.markBothEdges(proof)
        proof.conclusion.toSetSequent
      case h :: t =>
        t.foldLeft(safeLiteralsFromChild(h, proof, edgesToDelete)) { (acc, v) =>
          {
            smartIntersect(acc, safeLiteralsFromChild(v, proof, edgesToDelete))
          }
        }
    }
  }

  protected def smartIntersect(l: IClause, r: IClause) = {
    var out = Sequent()()
    val uVars = getSetOfVars(Axiom(l.toSeqSequent)) union getSetOfVars(Axiom(r.toSeqSequent))
    for (la <- l.ant) {
      for (ra <- r.ant) {
        unify((la, ra) :: Nil)(uVars) match {
          case None => {}
          case Some(sub) => {
            val newLA = getCleanLiteral(la, sub, out)
            out = newLA +: out
          }
        }
      }
    }

    for (ls <- l.suc) {
      for (rs <- r.suc) {
        unify((ls, rs) :: Nil)(uVars) match {
          case None => {}
          case Some(sub) => {
            val newLS = getCleanLiteral(ls, sub, out)
            out = out + newLS
          }
        }
      }
    }

    out.toSetSequent

  }

  def getCleanLiteral(l: E, s: Substitution, rest: Sequent) = {
    val restAx = Axiom(rest)
    val lsubbed = s(l)
    val lsAx = Axiom(Sequent(lsubbed)())
    val vars = getSetOfVars(restAx) union getSetOfVars(lsAx)

    val lsAxClean = fixSharedNoFilter(lsAx, restAx, 0, vars)

    val cleanL = lsAxClean.conclusion.ant.head

    cleanL
  }
}
