package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
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

  def getUnitLiteralUsingAux(p: SequentProofNode, u: SequentProofNode, node: SequentProofNode, vars: MSet[Var]) = {
    //TODO: support nodes with 3+ premises? Or just more than UR in general?
    
    val premise = node.premises.filter(_ != u).head 
    
    if(u.conclusion.ant.size > 0){
      node.asInstanceOf[UnifyingResolution].auxL
    } else {
      node.asInstanceOf[UnifyingResolution].auxR
    }
  }
  
  def getAuxVars(listOfUnits: List[E]) = {
    val out = MSet[Var]()
    for(e <- listOfUnits) {
      val eVars = getSetOfVars(e)
      for(v <- eVars){
        out.add(v)
      }
    }
    out
  }
  
  def collectUnits(proof: Proof[SequentProofNode]) = {
    val vars = MSet[Var]()
    val unitsList = (proof :\ (Nil: List[SequentProofNode])) { (node, acc) =>
      if (isUnitClause(node.conclusion) && proof.childrenOf(node).length > 1) {
        val children = proof.childrenOf(node)

        println("children are: " + children)
        //This gets the child of the unit, but really we want the other parent of the child of the unit.
        //so we do the following:
        val childrensParentsConclusionsSeqSeq = for (c <- children) yield {
          println("C ?? " + c)
          val parentsConclusions = for (p <- c.premises) yield {
            //Picks out (all) u_k in c_k
            println("all premises yo? " + p)
            
            val oo = getUnitLiteralUsingAux(p, node, c, vars)
            
            val o = getUnitLiteral(p.conclusion, node.conclusion, vars) //TODO: change this? use aux formula?
            println("ulbetter? " + oo)
                        println("ul: " + o)
            
            Seq[E](oo)
//            o

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

                println("L of U: " + listOfUnits) //TODO: list of units is incorrect. see above
        val varsN = getSetOfVars(node)
        for (v <- varsN) {
          vars += v
        }
        
        val auxVars = getAuxVars(listOfUnits)
        for(v <- auxVars) {
          vars += v
        }

        println("vars?" + vars)
        if (checkListUnif(listOfUnits, vars)) {
//          if(checkContraction(listOfUnits, vars, node)){
//            node :: acc
//          } else {
//            acc
//          }
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

  //TODO: causing loops. bad. fix.
  def checkContraction(listOfUnits: List[E], vars: MSet[Var], node: SequentProofNode): Boolean = {
    println("units? ? " + listOfUnits)
    val newSeq = addAntecedents(listOfUnits)
    val con = Contraction(Axiom(newSeq))(vars)
    println("newSeq? " + newSeq)
    println("con? " + con)
    
    val unitFormula = if(node.conclusion.ant.size > 0) {
      node.conclusion.ant.head
    } else {
      node.conclusion.suc.head
    }
    
    for(conForm <- con.conclusion.ant) {
      println("conform: " + conForm)
      println("unitform: " + unitFormula)
      if(!isUnifiable((conForm, unitFormula))(vars)){
        return false
      }
    }
    
    true
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
          l
        } else if (isUnifiable((unit.ant.head, l))(vars)) {
          l
        } else {
          null.asInstanceOf[E]
        }
      }
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
        println("checking: " + p)
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

    //TODO: needs to change to e.g., [Node, Sequent]
    //so that multiple carries make sense.
    val carryMap = MMap[SequentProofNode, Sequent]()
    //    val replaceMap = MMap[SequentProofNode, SequentProofNode]()
    val mguMap = MMap[SequentProofNode, Substitution]()

    def addToMap(k: SequentProofNode, carry: Sequent) = {
      if (carryMap.get(k).isEmpty) {
        carryMap.put(k, carry)
      } else {
        val existingCarry = carryMap.get(k).get
        val bothCarries = existingCarry union carry
        carryMap.update(k, bothCarries)
      }
    }

    //    println("units really are: " + unitsSet)
    def visit(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
      //      println("visiting: " + node)
      lazy val fixedLeft = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;

      println("visiting. MAP: " + carryMap)

      val fixedP = node match {
        case Axiom(conclusion) => node
        case UnifyingResolution(left, right, _, _) if unitsSet contains left => {
          //          println("unitset must have cotained one of " + left + " or " + right + " for " + node)
          //          println("using " + fixedRight + " for " + node.conclusion)
          //          println(fixedRight + " --r> " + node.asInstanceOf[UnifyingResolution].auxR)
          println("XX")
          carryMap.update(fixedRight, makeUnitSequent(left, node.asInstanceOf[UnifyingResolution].auxR))
          //          addToMap(fixedRight, makeUnitSequent(left, node.asInstanceOf[UnifyingResolution].auxR))
          mguMap.update(fixedRight, node.asInstanceOf[UnifyingResolution].mgu)
          fixedRight
        }
        case UnifyingResolution(left, right, _, _) if unitsSet contains right => {
          //          println("unitset must have cotained one of " + left + " or " + right + " for " + node)
          //          println("using " + fixedLeft + " for " + node.conclusion)
          //          println(fixedLeft + " --l> " + node.asInstanceOf[UnifyingResolution].auxL)
          println("YY")
          carryMap.update(fixedLeft, makeUnitSequent(right, node.asInstanceOf[UnifyingResolution].auxL))
          //          addToMap(fixedLeft, makeUnitSequent(right, node.asInstanceOf[UnifyingResolution].auxL))
          mguMap.update(fixedLeft, node.asInstanceOf[UnifyingResolution].mgu)

          fixedLeft
        }
        //Need MRR since we might have to contract, in order to avoid ambiguous resolution
        case UnifyingResolution(left, right, _, _) => {
          //          println("attempting to resolve the following:")
          //          println(node.conclusion)

          try {
            UnifyingResolutionMRR(fixedLeft, fixedRight)(vars)
          } catch {
            case e: Exception => {
              if (e.getMessage != null) {
                if (e.getMessage.equals("Resolution (MRR): the resolvent is ambiguous.")) {

                  println("caught for " + node)
                  println("fixed left: " + fixedLeft)
                  println("fixed right: " + fixedRight)
                  println(" (l: " + left + ")")
                  println(" (r: " + right + ")")
                  //
                  //                  println("nc: " + node.conclusion)

                  val oAuxL = node.asInstanceOf[UnifyingResolution].auxL
                  val oAuxR = node.asInstanceOf[UnifyingResolution].auxR
                  println("auxL: " + oAuxL)
                  println("auxR: " + oAuxR)
                  val oMGU = node.asInstanceOf[UnifyingResolution].mgu
                  //                  println("omgu: " + oMGU)

                  //                  val oldLeftClean = node.asInstanceOf[UnifyingResolution].leftClean
                  //                  val cleanMGU = findRenaming(left.conclusion, oldLeftClean.conclusion)(vars)
                  //                  println("oldLeftClean.conclusion " + oldLeftClean.conclusion)
                  //                  println("left.conclusion " + left.conclusion)
                  //                  println("cleanMGU?? " + cleanMGU)
                  println("cma[p: " + carryMap)
                  val carryA = if (!carryMap.get(fixedRight).isEmpty && !fixedRight.equals(right)) {
                    carryMap.get(fixedRight).get
                  } else { null }

                  val carryB = if (!carryMap.get(fixedLeft).isEmpty && !fixedLeft.equals(left)) {
                    carryMap.get(fixedLeft).get
                  } else { null }

                  println("carry (right): " + carryA)
                  println("carry (left ): " + carryB)

                  val olderA = if (!mguMap.get(fixedRight).isEmpty) {
                    mguMap.get(fixedRight).get
                  } else { null }

                  val olderB = if (!mguMap.get(fixedLeft).isEmpty) {
                    mguMap.get(fixedLeft).get
                  } else { null }

                  //                                    println("mguOld (right): " + olderA)
                  //                                    println("mguOld (left ): " + olderB)

                  val newFixedRight = fixedRight match {
                    case Axiom(c) if (olderA != null && !fixedRight.equals(right)) => {
                      new FOSubstitution(fixedRight, olderA)(vars)
                    }
                    case _ if (olderA != null && !fixedRight.equals(right)) => {
                      new FOSubstitution(fixedRight, olderA)(vars)
                    }
                    case _ => {
                      fixedRight
                    }
                  }

                  val newFixedLeft = fixedLeft match {
                    case Axiom(c) if (olderB != null && !fixedLeft.equals(left)) => {
                      new FOSubstitution(fixedLeft, olderB)(vars)
                    }
                    case _ if (olderB != null && !fixedLeft.equals(left)) => {
                      new FOSubstitution(fixedLeft, olderB)(vars)
                    }
                    case _ => {
                      fixedLeft
                    }
                  }

                  val (leftMGU, rightMGU) = splitMGU(node, left, right)

                  //                  println("newFR: " + newFixedRight)

                  //                  try {
                  //                    val stuff = test3(fixedLeft, fixedRight, carryA, carryB, olderA, olderB, node.conclusion, oMGU, node)(vars)
                  //                  val stuff = test4(fixedLeft, fixedRight, carryA, carryB, olderA, olderB, node.conclusion, oMGU, node)(vars)
                  val stuff = test5(fixedLeft, fixedRight, carryA, carryB, olderA, olderB, node.conclusion, oMGU, node, leftMGU, rightMGU)(vars)

                  val newGoalD = stuff._1
                  println("FINAL newGoalD: " + newGoalD)

                  println("newFixedRight: " + newFixedRight)
                  println("newFixedLeft: " + newFixedLeft)

                  val out = try {
                    UnifyingResolutionMRR(newFixedLeft, newFixedRight, newGoalD)(vars)
                  } catch {
                    case e: Exception => {
                      println("desperate... " + e.getMessage())
                      UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalD)(vars)
                      //                                            UnifyingResolutionMRR(newFixedRight, newFixedLeft, newGoalD)(vars)
                    }
                  }

                  //                    println("made it..")

                  //                    val out = UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalD)(vars)
                  println("FINAL COMPUTED: " + out.conclusion)

                  println("3:" + stuff._3)
                  println("4:" + stuff._4)

                  val mergedCarry = unionSequents(stuff._3, stuff._4)

                  //                  val oldLeftClean = node.asInstanceOf[UnifyingResolution].leftClean
                  val cleanMGU = findRenaming(newGoalD, out.conclusion)(vars)
                  println("newGoalD " + newGoalD)
                  println("out.conclusion " + out.conclusion)
                  println("cleanMGU?? " + cleanMGU)

                  val testCarry = if (mergedCarry != null) {
                    val testAnt = if (mergedCarry.ant != null) {
                      mergedCarry.ant.map(e => cleanMGU(e))
                    } else {
                      Seq[E]()
                    }
                    val testSuc = if (mergedCarry.suc != null) {
                      mergedCarry.suc.map(e => cleanMGU(e))
                    } else {
                      Seq[E]()
                    }
                    addAntecedents(testAnt.toList) union addSuccedents(testSuc.toList)
                  } else {
                    null
                  }
                  println("merged: " + mergedCarry)
                  println("test: " + testCarry)

                  println("putting " + testCarry + " on the map for " + out)
                  println("CM: before: " + carryMap)
                  carryMap.update(out, testCarry)
                  println("CM: after: " + carryMap)
                  //                  carryMap.update(out, mergedCarry)

                  //                  println("OUTMGU: " + out.asInstanceOf[UnifyingResolutionMRR].mgu)
                  println("BUT SAID: " + stuff._2)
                  mguMap.update(out, stuff._2)
                  out

                } else {
                  println("compression failed - A - " + e.getMessage())
                  println(fixedRight)
                  println(fixedLeft)
                  //                  throw new Exception("Compression failed! A")
                  println(vars)
                  UnifyingResolutionMRR(fixedRight, fixedLeft)(vars)
                }
              } else {
                throw new Exception("Compression failed! B")
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

  def unionSequents(a: Sequent, b: Sequent): Sequent = {
    if (a != null && b != null) {
      a.union(b)
    } else if (a != null && b == null) {
      a
    } else if (a == null && b != null) {
      b
    } else {
      null
    }
  }

  def makeUnitSequent(u: SequentProofNode, c: E): Sequent = {
    if (isUnitAnt(u)) {
      Sequent()(c)
    } else {
      Sequent(c)()
    }
  }

  def isUnitAnt(u: SequentProofNode): Boolean = {
    if (u.conclusion.ant.size > 0) {
      true
    } else if (u.conclusion.suc.size > 0) {
      false
    } else {
      throw new Exception("Unit check on non-unit node")
    }
  }

  def splitMGU(p: SequentProofNode, l: SequentProofNode, r: SequentProofNode): (Substitution, Substitution) = {
    val ur = p.asInstanceOf[UnifyingResolution]
    val lCleanVars = getSetOfVars(ur.leftClean)
    val rVars = getSetOfVars(r)

    val oldMGU = ur.mgu

    val leftSubOutPairs = MSet[(Var, E)]()
    val rightSubOutPairs = MSet[(Var, E)]()

    for (s <- oldMGU) {
      if (rVars.contains(s._1)) {
        rightSubOutPairs.add(s)
      } else {
        leftSubOutPairs.add(s)
      }
    }

    val lSubOut = Substitution(leftSubOutPairs.toList: _*)
    val rSubOut = Substitution(rightSubOutPairs.toList: _*)

    (lSubOut, rSubOut)
  }

  def test5(fl: SequentProofNode, fr: SequentProofNode, carry: Sequent, carryB: Sequent, older: Substitution,
    olderB: Substitution, oldGoal: Sequent, nodeMGU: Substitution, n: SequentProofNode, lMGU: Substitution, rMGU: Substitution)(implicit uVars: MSet[Var]): (Sequent, Substitution, Sequent, Sequent) = {

    println("lMGU: " + lMGU)
    println("rMGU: " + rMGU)

    val temp = n // UnifyingResolution(newNodeB, newNodeA, oldGoal)

    val tempMGU = nodeMGU // temp.mgu

    println("TEMP: " + temp)
    println("carry: " + carry)
    println("carrB: " + carryB)
    //    println("TEMP MGU: " + temp.mgu )
    //    println("new goal SHOULD HAVE " + temp.mgu(older(carry)))

    val outSeq = if (carryB != null && carry != null) {
      //            addAntecedents(
      //              (temp.conclusion.ant.toList
      //                ++ carry.ant.map(e => tempMGU((e)))
      //                ++ carryB.ant.map(e => tempMGU((e))))) union addSuccedents(
      //                (temp.conclusion.suc.toList
      //                  ++ carry.suc.map(e => tempMGU((e)))
      //                  ++ carryB.suc.map(e => tempMGU((e)))))
      //      addAntecedents(
      //        (temp.conclusion.ant.toList
      //          ++ carry.ant.map(e => rMGU((e)))
      //          ++ carryB.ant.map(e => lMGU((e))))) union addSuccedents(
      //          (temp.conclusion.suc.toList
      //            ++ carry.suc.map(e => rMGU((e)))
      //            ++ carryB.suc.map(e => lMGU((e)))))

      //      addAntecedents(
      //        (temp.conclusion.ant.toList
      //          ++ carry.ant
      //          ++ carryB.ant)) union addSuccedents(
      //          (temp.conclusion.suc.toList
      //            ++ carry.suc
      //            ++ carryB.suc))  
      println("A")
      addAntecedents(
        (temp.conclusion.ant.toList
          ++ carry.ant.map(e => older((e))).map(e => rMGU(e))
          ++ carryB.ant.map(e => olderB((e))).map(e => lMGU(e)))) union addSuccedents(
          (temp.conclusion.suc.toList
            ++ carry.suc.map(e => older((e))).map(e => rMGU(e))
            ++ carryB.suc.map(e => olderB((e))).map(e => lMGU(e))))

    } else if (carry == null && carryB != null) {
      println("B")

      addAntecedents((temp.conclusion.ant.toList
        //lMGU was tempMGU
        //        ++ carryB.ant.map(e => lMGU((e))))) union addSuccedents(temp.conclusion.suc.toList ++ carryB.suc.map(e => lMGU(e)))
        //        ++ carryB.ant.map(e => tempMGU((e))))) union addSuccedents(temp.conclusion.suc.toList ++ carryB.suc.map(e => tempMGU(e)))
        ++ carryB.ant.map(e => olderB((e))).map(e => lMGU(e)))) union addSuccedents(temp.conclusion.suc.toList ++ carryB.suc.map(e => olderB((e))).map(e => lMGU(e)))

      //        ++ carryB.ant)) union addSuccedents(temp.conclusion.suc.toList ++ carryB.suc)

    } else if (carry != null && carryB == null) {
      println("C")
      //      addAntecedents((temp.conclusion.ant.toList ++ carry.ant.map(e => tempMGU((e))))) union addSuccedents(temp.conclusion.suc.toList ++ carry.suc.map(e => tempMGU((e))))
      //      addAntecedents((temp.conclusion.ant.toList ++ carry.ant.map(e => rMGU((e))))) union addSuccedents(temp.conclusion.suc.toList ++ carry.suc.map(e => rMGU((e))))

      addAntecedents((temp.conclusion.ant.toList ++ carry.ant.map(e => older((e))).map(e => rMGU(e)))) union addSuccedents(temp.conclusion.suc.toList ++ carry.suc.map(e => older((e))).map(e => rMGU((e))))

      //      addAntecedents((temp.conclusion.ant.toList ++ carry.ant)) union addSuccedents(temp.conclusion.suc.toList ++ carry.suc)

    } else {
      println("D")
      addAntecedents(temp.conclusion.ant.toList) union addSuccedents(temp.conclusion.suc.toList)
    }

    //    println("final? : " +  outSeq)

    var outB = null.asInstanceOf[Sequent]
    if (carryB != null) {
      //            val newAnt = carryB.ant.map(e => olderB(e)).map(e => tempMGU(e))
      //            val newSuc = carryB.suc.map(e => olderB(e)).map(e => tempMGU(e))

      val newAnt = carryB.ant.map(e => olderB(e)).map(e => lMGU(e))
      val newSuc = carryB.suc.map(e => olderB(e)).map(e => lMGU(e))

      //      val newAnt = carryB.ant.map(e => tempMGU(e))
      //      val newSuc = carryB.suc.map(e => tempMGU(e))

      //      val newAnt = carryB.ant.map(e => lMGU(e))
      //      val newSuc = carryB.suc.map(e => lMGU(e))
      outB = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
    }

    println("older: " + older)
    println("oldeB: " + olderB)
    println("tmp: " + tempMGU)

    var outA = null.asInstanceOf[Sequent]
    if (carry != null) {
      //            val newAnt = carry.ant.map(e => older(e)).map(e => tempMGU(e))
      //            val newSuc = carry.suc.map(e => older(e)).map(e => tempMGU(e))

      val newAnt = carry.ant.map(e => older(e)).map(e => rMGU(e))
      val newSuc = carry.suc.map(e => older(e)).map(e => rMGU(e))
      //      val newAnt = carry.ant.map(e => tempMGU(e))
      //      val newSuc = carry.suc.map(e => tempMGU(e))

      //      val newAnt = carry.ant.map(e => rMGU(e))
      //      val newSuc = carry.suc.map(e => rMGU(e))
      outA = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
    }

    println("outa: " + outA)
    println("outb: " + outB)
    (outSeq, tempMGU, outA, outB)
  }

  //
  def findUnifiableFormula(f: E, seqHalf: Seq[E])(implicit uVars: MSet[Var]): MSet[E] = {
    val out = MSet[E]()
    println("vars : " + uVars)
    for (sf <- seqHalf) {
      println("f: " + f)
      println("sf: " + sf)
      if (isUnifiable((f, sf))) {
        //        println("X")
        out.add(sf)
      }
      if (isUnifiable((sf, f))) {
        //        println("Y")
        out.add(sf)
      }
    }
    out
  }

  def contractAndUnify(left: SequentProofNode, right: SequentProofNode, vars: MSet[Var]) = {
    println("c and u")
    println("l: " + left)
    println("r: " + right)
    if (isUnitClause(left.conclusion)) {
      if (isUnitClause(right.conclusion)) {
        //        println("A")
        //Both units; no need to contract either
        UnifyingResolution(left, right)(vars)

      } else {
        //only right is non-unit
        val contracted = Contraction(right)(vars)
        if (contracted.conclusion.logicalSize < right.conclusion.logicalSize) {
          finishResolution(left, contracted, true)(vars)
        } else {
          finishResolution(left, right, true)(vars)
        }
      }
    } else {
      if (isUnitClause(right.conclusion)) {
        //only left is non-unit
        val contracted = Contraction(left)(vars)
        if (contracted.conclusion.logicalSize < left.conclusion.logicalSize) {
          finishResolution(contracted, right, false)(vars)
        } else {
          finishResolution(left, right, false)(vars)

        }
      } else {
        //both are non-units
        UnifyingResolution(left, right)(vars)
      }
    }
  }

  def finishResolution(left: SequentProofNode, right: SequentProofNode, leftIsUnit: Boolean)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    try {
      UnifyingResolution(left, right)(unifiableVariables)
    } catch {
      case e: Exception => {
        //TODO: make sure it's the exception we want (ambiguous resolution)
        multipleResolution(left, right, leftIsUnit)(unifiableVariables)
      }
    }
  }

  //TODO: can probably avoid code reuse by introducing helper functions
  def multipleResolution(left: SequentProofNode, right: SequentProofNode, leftIsUnit: Boolean)(implicit unifiableVariables: MSet[Var]): SequentProofNode = {
    println("left: " + left)
    println("right: " + right)
    println("b: " + leftIsUnit)
    if (leftIsUnit) {
      //left is unit
      if (left.conclusion.suc.size > 0) {
        val leftUnit = left.conclusion.suc.head
        val toRemove = findUnifiableFormula(leftUnit, right.conclusion.ant).head
        val newAnt = right.conclusion.ant.filter(_ != toRemove)
        val newSuc = right.conclusion.suc
        val goal = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
        val temp = UnifyingResolution(left, right, goal)
        if (temp.conclusion.ant.size == 0 && temp.conclusion.suc.size == 0) {
          temp
        } else {
          multipleResolution(left, temp, leftIsUnit)
        }
      } else if (left.conclusion.ant.size > 0) {
        val leftUnit = left.conclusion.ant.head
        val toRemove = findUnifiableFormula(leftUnit, right.conclusion.suc).head
        val newAnt = right.conclusion.ant
        val newSuc = right.conclusion.suc.filter(_ != toRemove)
        val goal = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
        val temp = UnifyingResolution(left, right, goal)
        if (temp.conclusion.ant.size == 0 && temp.conclusion.suc.size == 0) {
          temp
        } else {
          multipleResolution(left, temp, leftIsUnit)
        }
      } else {
        null //stub; error //TODO: this
      }
    } else {
      if (right.conclusion.suc.size > 0) {
        val rightUnit = right.conclusion.suc.head
        val toRemove = findUnifiableFormula(rightUnit, left.conclusion.ant).head
        val newAnt = left.conclusion.ant.filter(_ != toRemove)
        val newSuc = left.conclusion.suc
        val goal = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
        val temp = UnifyingResolution(left, right, goal)
        if (temp.conclusion.ant.size == 0 && temp.conclusion.suc.size == 0) {
          temp
        } else {
          multipleResolution(left, temp, leftIsUnit)
        }
      } else if (right.conclusion.ant.size > 0) {
        val rightUnit = right.conclusion.ant.head
        //        println("ru: " + rightUnit)
        //        println("lcs: " + left.conclusion.suc)
        //        println("aaa: " + findUnifiableFormula(rightUnit, left.conclusion.suc))
        val toRemove = findUnifiableFormula(rightUnit, left.conclusion.suc).head
        val newAnt = left.conclusion.ant
        val newSuc = left.conclusion.suc.filter(_ != toRemove)
        val goal = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
        val temp = UnifyingResolution(left, right, goal)
        if (temp.conclusion.ant.size == 0 && temp.conclusion.suc.size == 0) {
          temp
        } else {
          multipleResolution(left, temp, leftIsUnit)
        }
      } else {
        null //stub; error //TODO: this
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
      //      println("left: " + left)
      //      println("right: " + right)
      try {
        contractAndUnify(left, right, vars)
      } catch {
        case e: Exception => {
          e.printStackTrace()

          contractAndUnify(right, left, vars)
        }
      }
    }

    //    println("fixMap built")
    //        for (k <- fixMap.keySet) {
    //          println(k + " -----> " + fixMap.get(k))
    //        }

    val root = units.map(fixMap).foldLeft(fixMap(proof.root))(placeLoweredResolution)

    val p = Proof(root)
    p
  }

}
