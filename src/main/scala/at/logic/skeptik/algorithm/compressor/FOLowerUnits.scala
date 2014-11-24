package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.Contraction
import at.logic.skeptik.proof.sequent.resolution.CanRenameVariables
import at.logic.skeptik.proof.sequent.resolution.FindDesiredSequent
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import collection.mutable.{ Queue, HashMap => MMap }
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.expression._
import collection.mutable.{ HashSet => MSet }
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }
import at.logic.skeptik.parser.ProofParserSPASS.addAntecedents
import at.logic.skeptik.parser.ProofParserSPASS.addSuccedents
import at.logic.skeptik.expression.substitution.immutable.Substitution

object FOLowerUnits
  extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with CanRenameVariables with FindDesiredSequent {

  def isUnitClause(s: Sequent) = s.ant.length + s.suc.length == 1

  // ToDo: optimize this by interlacing collectUnits and fixProofNodes

  def cleanUpLists(in: IndexedSeq[Seq[Seq[E]]]) = {
    var out = List[E]()
    for (outer <- in) {
      for (inner <- outer) {
        out = out ++ inner
      }
    }

    out.distinct
  }

  def collectUnits(proof: Proof[SequentProofNode]) = {
    val vars = MSet[Var]()
    val unitsList = (proof :\ (Nil: List[SequentProofNode])) { (node, acc) =>
      if (isUnitClause(node.conclusion) && proof.childrenOf(node).length > 1) {
        val children = proof.childrenOf(node)

        //        println("children are: " + children)
        //This gets the child of the unit, but really we want the other parent of the child of the unit.
        //so we do the following:
        val childrensParentsConclusionsSeqSeq = for (c <- children) yield {
          val parentsConclusions = for (p <- c.premises) yield {
            //Picks out (all) u_k in c_k
            val o = getUnitLiteral(p.conclusion, node.conclusion, vars) //
            //            println("ul: " + o)
            o

          }
          val varsC = getSetOfVars(c)
          for (v <- varsC) {
            vars += v
          }
          parentsConclusions.filter(_.length > 0)
        }
        //        println("big: " + childrensParentsConclusionsSeqSeq)
        //        cleanUpLists(childrensParentsConclusionsSeqSeq)
        //        val listOfUnits = childrensParentsConclusionsSeqSeq(0).flatten.toList//this line is bugged!
        //        //why use only the first entry! that's wrong!

        val listOfUnits = cleanUpLists(childrensParentsConclusionsSeqSeq)

        //        println("L of U: " + listOfUnits)
        val varsN = getSetOfVars(node)
        for (v <- varsN) {
          vars += v
        }

        if (checkListUnif(listOfUnits, vars)) {
          node :: acc
        } else {
          acc
        }

      } else {
        val varsN = getSetOfVars(node)
        for (v <- varsN) {
          vars += v
        }
        acc
      }
    }
    (unitsList, vars)
  }

  def getUnitLiteral(seq: Sequent, unit: Sequent, vars: MSet[Var]) = {
    //    println("checking for " + unit + " in " + seq)
    if (unit.ant.length > 0) {
      //positive polarity, only need to check negative polarity of seq

      val varsN = getSetOfVars(seq.suc: _*)
      for (v <- varsN) {
        vars += v
      }

      val out = for (l <- seq.suc) yield {
        //        println("l: " + l)
        if (isUnifiable((l, unit.ant.head))(vars)) {
          //          println("good")
          l
        } else if (isUnifiable((unit.ant.head, l))(vars)) {
          //          println("better")
          l
        } else {
          null.asInstanceOf[E]
        }
      }
      //      println("out: " + out)
      //      println("out filtered: " + out.filter(_ != null))
      out.filter(_ != null)
    } else if (unit.suc.length > 0) {
      //negative polarity, only need to check positive polarity of seq

      val varsN = getSetOfVars(seq.ant: _*)
      for (v <- varsN) {
        vars += v
      }

      val out = for (l <- seq.ant) yield {
        if (isUnifiable((l, unit.suc.head))(vars)) {
          l
        } else if (isUnifiable((unit.suc.head, l))(vars)) {
          l
        } else {
          null.asInstanceOf[E]
        }
      }
      out.filter(_ != null)
    } else {
      Seq[E]()
    }
  }

  def checkListUnif(l: List[E], vars: MSet[Var]): Boolean = {
    //    println("list: " + l)
    if (l.length > 1) {
      val first = l.head
      val second = l.tail.head

      def isUnifiableWrapper(p: (E, E)) = {
        isUnifiable(p)(vars)
      }

      val mguResult = isUnifiable(first, second)(vars)

      if (mguResult) {
        checkListUnif(l.tail, vars)
      } else {
        false
      }
    } else if (l.length == 0) {
      //found no pair-wise unifiable list, so we don't lower this unit.
      false
    } else {
      true
    }
  }

  def childrenOfFixed(proof: Proof[SequentProofNode], node: SequentProofNode, vars: MSet[Var]): IndexedSeq[SequentProofNode] = {
    if (proof.childrenOf.contains(node)) {
      proof.childrenOf.get(node).get
    } else {
      for (n <- proof) {
        if (desiredFound(n.conclusion, node.conclusion)(vars)) {
          return proof.childrenOf.get(n).get
        }
      }
      IndexedSeq[SequentProofNode]()
    }
  }

  def fixProofNodes(unitsSet: Set[SequentProofNode], proof: Proof[SequentProofNode], vars: MSet[Var]) = {
    val fixMap = MMap[SequentProofNode, SequentProofNode]()

    //    println("units really are: " + unitsSet)
    def visit(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
      //      println("visiting: " + node)
      lazy val fixedLeft = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;

      val fixedP = node match {
        case Axiom(conclusion) => node
        case UnifyingResolution(left, right, _, _) if unitsSet contains left => {
          //          println("unitset must have cotained one of " + left + " or " + right + " for " + node)
          //          println("using " + fixedRight)
          fixedRight
        }
        case UnifyingResolution(left, right, _, _) if unitsSet contains right => {
          //          println("unitset must have cotained one of " + left + " or " + right + " for " + node)
          //          println("using " + fixedLeft)
          fixedLeft
        }
        //Need MRR since we might have to contract, in order to avoid ambiguous resolution
        case UnifyingResolution(left, right, _, _) => {
          //          println("attempting to resolve the following:")
          //          println("left: " + fixedLeft + " (l: " + left + ")")
          //          println("right: " + fixedRight + " (r: " + right + ")")
          //          println(vars)
          try {
            UnifyingResolutionMRR(fixedLeft, fixedRight)(vars)
          } catch {
            case e: Exception => {
              if (e.getMessage != null) {
                if (e.getMessage.equals("Resolution (MRR): the resolvent is ambiguous.")) {
                  println("caught for " + node)
                  println("left: " + fixedLeft + " (l: " + left + ")")
                  println("right: " + fixedRight + " (r: " + right + ")")
                  //                  println(proof.childrenOf.contains(fixedLeft))
                  //                  println(proof.childrenOf.contains(fixedRight))

                  val frChildren = childrenOfFixed(proof, fixedRight, vars)
                  val flChildren = childrenOfFixed(proof, fixedLeft, vars)

                  //                                    val flChildren = proof.childrenOf.get(fixedLeft).get
                  //                                    val frChildren = proof.childrenOf.get(fixedRight).get
                  //                  val flChildren = proof.childrenOf.get(left).get
                  //                  val frChildren = proof.childrenOf.get(right).get 

                  println("flC: " + flChildren)
                  println("frC: " + frChildren)

                  //instead of this, look for the fixed left or fixed right that does not contain
                  //a unit, but should contain a unit.
                  //and try all subsets of the lowered units with it until we find the corresponding
                  //original left or right node (when it's unified, we know we've found it)
                  //then, use the original conclusion with the opposite of each unit found
                  //as the desired sequent, thereby avoiding ambiguous resolution errors.
                  //                  checkResolvent(unitsSet, right, fixedRight)(vars)//test this
                  //                  checkResolvent(unitsSet, fixedRight, right)(vars)//test this
                  println("nc: " + node.conclusion)
                  //                  val newGoal = addUnit(node.conclusion, unitsSet)
                  //                  println("new goal: " + newGoal)
                  println("auxL: " + node.asInstanceOf[UnifyingResolution].auxL)
                  println("auxR: " + node.asInstanceOf[UnifyingResolution].auxR)
                  println(node.asInstanceOf[UnifyingResolution].mgu)

                  val carry = findCorrected(node.asInstanceOf[UnifyingResolution].auxR, unitsSet.head.conclusion.suc.head,
                    fixedRight, right.conclusion, true, node.asInstanceOf[UnifyingResolution].mgu)(vars)
                  val newGoal = addCarry(node.conclusion, carry._1, unitsSet.head)
                  println("newGoal: " + newGoal)
                  
                  //                  findOriginal(unitsSet.head, fixedLeft, right, fixedRight, node.conclusion)(vars)

                  //                  println("success: " + UnifyingResolutionMRR(fixedLeft, fixedRight, newGoal)(vars))
//                  val child = flChildren.intersect(frChildren).head
                  //                  println("child: " + child)
                  //                  println("node: " + node)
                  
                  UnifyingResolutionMRR(fixedRight, fixedLeft, newGoal, carry._2)(vars)
                } else {
                  throw new Exception("Compression failed!")
                }
              } else {
                throw new Exception("Compression failed!")
              }
            }
          }
        }
        case Contraction(_, _) => {
          //For contractions, we pick a fixed node (but both are equal, so either works)
          //the fixed node is the same as the contraction syntactically, but has
          //the correct premise node in the fixed proof
          assert(fixedLeft == fixedRight)
          fixedRight
        }
        case _ => {
          node
        }
      }
      if (node == proof.root || unitsSet.contains(node)) {
        println("updating map: " + node + " ---> " + fixedP)
        fixMap.update(node, fixedP)
      }
      //      println("node: " + node)
      //      println("fixedP: " + fixedP)
      fixedP
    }
    proof.foldDown(visit)
    fixMap
  }

  def addCarry(con: Sequent, carry: E, unit: SequentProofNode): Sequent = {
    if(unit.conclusion.ant.size > 0){
      addAntecedents(con.ant.toList) union addSuccedents(con.suc.toList ++ List[E](carry))
    } else if (unit.conclusion.suc.size > 0){
      addAntecedents(con.ant.toList ++ List[E](carry)) union addSuccedents(con.suc.toList)
    } else {
      null
    }
  }
  
  //
  //TODO: consider case where aux in suc
  def findCorrected(aux: E, unit: E, fixed: SequentProofNode, original: Sequent, auxInAnt: Boolean, mgu: Substitution)
  (implicit uVars: MSet[Var]): (E, Substitution) = {
    if (auxInAnt) {
      for (f <- fixed.conclusion.ant) {
        val u = getUnifier((f, aux))
//        val u = getUnifier((aux, f))
        
        def filterFunc(expr: E)(implicit uVars: MSet[Var]): Boolean = {
          !desiredFound(Sequent(expr)(), Sequent(unit)())
        }

        if (u != null) {
//          println("ant before filter: " + fixed.conclusion.ant.map(e => u(e)).filter(filterFunc))
          val newAnt = fixed.conclusion.ant.map(e => u(e)).filter(filterFunc)
          
          val newSuc = fixed.conclusion.suc.map(e => u(e))
          val newConclusion = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
          println("u: " + u)
//          println("newCon: " + newConclusion)
//          println("original: " + original)
          if (desiredFound(newConclusion, original)) {
            println("F: " + f)
//            println("newUnit: " + mgu(u(unit)))
            return (mgu(u(unit)), u)
          }
        }
      }
      null
    }
    null
  }

  //remove things from the fixed, until we *can* find the original
  //then the thing removed must have been removed by resolution with a unit
  //in the original proof.

  //assume left is good
  def findOriginal(unit: SequentProofNode, left: SequentProofNode, right: SequentProofNode, rightFixed: SequentProofNode, originalSeq: Sequent)(implicit unifiableVars: MSet[Var]) = {
    println("os: " + originalSeq)
    if (unit.conclusion.suc.size > 0) {
      //find something to remove from the fixed entry
      val us = findUnifiableFormula(unit.conclusion.suc.head, rightFixed.conclusion.ant)
      for (uf <- us) {
        //    	val uf = findUnifiableFormula(unit.conclusion.suc.head, rightFixed.conclusion.ant)
        val newRightConclusionAnt = rightFixed.conclusion.ant.filter(_ != uf)
        val newRightConclusion = addAntecedents(newRightConclusionAnt.toList) union addSuccedents(rightFixed.conclusion.suc.toList)
        //addSuccedents(newRightConclusionSuc.toList) union addAntecedents(rightFixed.conclusion.ant.toList)
        println("newRightConclusion: " + newRightConclusion)
        val newRightBeforeUni = Axiom(newRightConclusion)

        val newRight = unifySequents(right, newRightBeforeUni)
        println("newRight: " + newRight)
        try {
          UnifyingResolution(left, newRight, originalSeq)
          println("X")
        } catch {
          case e: Exception => {}
        }
      }
    }
  }

  //
  def unifySequents(right: SequentProofNode, newRight: SequentProofNode)(implicit uVars: MSet[Var]): SequentProofNode = {
    if (desiredFound(right.conclusion, newRight.conclusion)) {
      right
    } else {
      null
    }
  }

  //
  def findUnifiableFormula(f: E, seqHalf: Seq[E])(implicit uVars: MSet[Var]): MSet[E] = {
    val out = MSet[E]()
    for (sf <- seqHalf) {
      if (isUnifiable((f, sf))) {
        out.add(sf)
      }
      if (isUnifiable((sf, f))) {
        out.add(sf)
      }
    }
    out
  }

  //
  def addUnit(con: Sequent, units: Set[SequentProofNode]): Sequent = {
    if (units.size < 1) { return null }
    val u = units.head
    if (u.conclusion.ant.size > 0) {
      val newAnt = addAntecedents(con.ant.toList)
      val newSuc = addSuccedents(con.suc.toList ++ u.conclusion.ant.toList)
      val newConclusion = newSuc union newAnt
      newConclusion
    } else if (u.conclusion.suc.size > 0) {
      val newAnt = addAntecedents(con.ant.toList ++ u.conclusion.suc.toList)
      val newSuc = addSuccedents(con.suc.toList)
      val newConclusion = newSuc union newAnt
      newConclusion
    } else {
      throw new Exception("FOLowerUnits can't find the thing")
    }

  }

  //untested
  def checkResolvent(units: Set[SequentProofNode], actual: SequentProofNode, fixed: SequentProofNode)(implicit unifiableVars: MSet[Var]): Sequent = {
    println("Enterted checkResolvent")
    println("a: " + actual)
    println("f: " + fixed)
    println("u: " + units)
    if (units.size < 1) { return null }
    val u = units.head
    if (u.conclusion.ant.size > 0) {
      val newAnt = addAntecedents(actual.conclusion.ant.toList)
      val newSuc = addSuccedents(actual.conclusion.suc.toList ++ u.conclusion.ant.toList)
      val newConclusion = newSuc union newAnt
      if (desiredFound(fixed.conclusion, newConclusion)(unifiableVars) ||
        desiredFound(newConclusion, fixed.conclusion)(unifiableVars)) {
        return newConclusion
      } else {
        val recursiveA = checkResolvent(units.tail, actual, Axiom(newConclusion))
        val recursiveB = checkResolvent(units.tail, actual, fixed)

        if (recursiveA != null) {
          return recursiveA
        } else if (recursiveB != null) {
          return recursiveB
        } else {
          throw new Exception("FOLowerUnits Failed A")
        }
      }

    } else if (u.conclusion.suc.size > 0) {
      val newAnt = addAntecedents(actual.conclusion.ant.toList ++ u.conclusion.suc.toList)
      val newSuc = addSuccedents(actual.conclusion.suc.toList)
      val newConclusion = newSuc union newAnt
      println("nc: " + newConclusion)
      if (desiredFound(fixed.conclusion, newConclusion)(unifiableVars) ||
        desiredFound(newConclusion, fixed.conclusion)(unifiableVars)) {
        return newConclusion
      } else {
        val recursiveA = checkResolvent(units.tail, actual, Axiom(newConclusion))
        val recursiveB = checkResolvent(units.tail, actual, fixed)

        if (recursiveA != null) {
          return recursiveA
        } else if (recursiveB != null) {
          return recursiveB
        } else {
          throw new Exception("FOLowerUnits Failed B")
        }
      }

    } else {
      throw new Exception("FOLowerUnits failed")
    }

  }

  def contractAndUnify(left: SequentProofNode, right: SequentProofNode, vars: MSet[Var]) = {
    if (isUnitClause(left.conclusion)) {
      if (isUnitClause(right.conclusion)) {
        //Both units; no need to contract either
        UnifyingResolution(left, right)(vars)

      } else {
        //only right is non-unit
        val contracted = Contraction(right)(vars)
        if (contracted.conclusion.logicalSize < right.conclusion.logicalSize) {
          UnifyingResolution(left, contracted)(vars)
        } else {
          UnifyingResolution(left, right)(vars)
        }
      }
    } else {
      if (isUnitClause(right.conclusion)) {
        //only left is non-unit
        val contracted = Contraction(left)(vars)
        if (contracted.conclusion.logicalSize < left.conclusion.logicalSize) {
          UnifyingResolution(contracted, right)(vars)
        } else {
          UnifyingResolution(left, right)(vars)

        }
      } else {
        //both are non-units
        UnifyingResolution(left, right)(vars)
      }
    }
  }

  def apply(proof: Proof[SequentProofNode]): Proof[SequentProofNode] = {
    val collected = collectUnits(proof)

    val units = collected._1
    val vars = collected._2

    println("lowerable units are: " + units)

    if (units.length == 0) {
      return proof
    }

    val fixMap = fixProofNodes(units.toSet, proof, vars)

    def placeLoweredResolution(left: SequentProofNode, right: SequentProofNode) = {
      try {
        //        println("A")
        contractAndUnify(left, right, vars)
      } catch {
        case e: Exception => {
          //          println("B")
          e.printStackTrace()
          contractAndUnify(right, left, vars)
        }
      }
    }

    println("fixMap built")
    //    for (k <- fixMap.keySet) {
    //      println(k + " -----> " + fixMap.get(k))
    //    }

    val root = units.map(fixMap).foldLeft(fixMap(proof.root))(placeLoweredResolution)

    val p = Proof(root)
    p
  }

}
