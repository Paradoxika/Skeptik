package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.FOSubstitution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.MRRException
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

    //    val premise = node.premises.filter(_ != u).head 

    //    println(" u " + u)
    //    println(" p? " + p)
    //    println(" node? " + node.asInstanceOf[UnifyingResolution])

    val cleanMGU = if (!node.asInstanceOf[UnifyingResolution].leftPremise.equals(u)) {
      val newVars = vars union getSetOfVars(node.asInstanceOf[UnifyingResolution].leftClean)
      //      println(newVars + " nv ")
      //      findRenaming(node.asInstanceOf[UnifyingResolution].leftPremise.conclusion, 
      //          node.asInstanceOf[UnifyingResolution].leftClean.conclusion)(newVars)
      findRenaming(node.asInstanceOf[UnifyingResolution].leftClean.conclusion,
        node.asInstanceOf[UnifyingResolution].leftPremise.conclusion)(newVars)

    } else {
      Substitution()
    }

    //    println("CLEAN MGU? " + cleanMGU + " vars " + vars)

    if (u.conclusion.ant.size > 0) {
      cleanMGU(node.asInstanceOf[UnifyingResolution].auxL)
    } else {
      node.asInstanceOf[UnifyingResolution].auxR
    }
  }

  def getAuxVars(listOfUnits: List[E]) = {
    val out = MSet[Var]()
    for (e <- listOfUnits) {
      val eVars = getSetOfVars(e)
      for (v <- eVars) {
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
          //          println("C ?? " + c)
          val parentsConclusions = for (p <- c.premises) yield {
            //Picks out (all) u_k in c_k
            //            println("all premises yo? " + p)

            val oo = getUnitLiteralUsingAux(p, node, c, vars)

            val o = getUnitLiteral(p.conclusion, node.conclusion, vars) //TODO: change this? use aux formula?
            //            println("ulbetter? " + oo)
            //                        println("ul: " + o)

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
        for (v <- auxVars) {
          vars += v
        }

        //        println("vars?" + vars)
        if (checkListUnif(listOfUnits, vars)) {
          if (checkContraction(listOfUnits, vars, node)) {
            node :: acc
          } else {
            acc
          }
          //          node :: acc
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

    //    val con = Contraction(Axiom(newSeq))(vars)
    val con = try {
      Contraction(Axiom(newSeq))(vars)
    } catch {
      case e: Exception => { null }
    }

    if (con == null) {
      return false
    }

    println("newSeq? " + newSeq)
    println("con? " + con)

    val unitFormula = if (node.conclusion.ant.size > 0) {
      node.conclusion.ant.head
    } else {
      node.conclusion.suc.head
    }

    for (conForm <- con.conclusion.ant) {
      println("conform: " + conForm)

      //    val cleanUnitFormula = fixSharedNoFilter(Axiom(Sequent(unitFormula)()), Axiom(Sequent(conForm)()), 0, vars).conclusion.ant.head  

      println("unitform: " + unitFormula)

      if (!isUnifiable((conForm, unitFormula))(vars)) {
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

  def tryReversingArguments(l: SequentProofNode, r: SequentProofNode, goal: Sequent, vars: MSet[Var]) = {
    try {
      UnifyingResolutionMRR(r, l, goal)(vars)
      println("pass????")
    } catch {
      case e: Exception => {
        println(e)
      }
    }
  }

  def updateCarry(oldCarry: Sequent, sub: Substitution): Sequent = {
    if (oldCarry == null) {
      return null.asInstanceOf[Sequent]
    }
    val updatedCarry = if (sub != null) {
      val updatedAnt = if (oldCarry.ant != null) {
        oldCarry.ant.map(e => sub(e)).toList
      } else {
        List[E]()
      }
      val updatedSuc = if (oldCarry.suc != null) {
        oldCarry.suc.map(e => sub(e)).toList
      } else {
        List[E]()
      }
      addAntecedents(updatedAnt) union addSuccedents(updatedSuc)
    } else {
      oldCarry
    }
    updatedCarry
  }

  def getRenamedMGU(original: Sequent, clean: Sequent, sub: Substitution, vars: MSet[Var]): Substitution = {
    val renamingForward = findRenaming(original, clean)(vars)
    if (renamingForward.size == 0) {
      return sub
    }

    val renamingBackward = findRenaming(clean, original)(vars)

    println("GRM: forward: " + renamingForward)
    println("GRM: backward: " + renamingBackward)

    def appSub(pair: (Var, E)): (Var, E) = {
      //      (renaming(pair._1).asInstanceOf[Var], sub(pair._2))
      if (!renamingForward.get(pair._1).isEmpty) {
        (renamingForward(pair._1).asInstanceOf[Var], pair._2)
      } else {
        (renamingBackward(pair._1).asInstanceOf[Var], pair._2)
      }

    }

    val outPairs = sub.toList.map(p => appSub(p))

    Substitution(outPairs: _*)
  }

  def fixProofNodes(unitsSet: Set[SequentProofNode], proof: Proof[SequentProofNode], vars: MSet[Var]) = {
    val fixMap = MMap[SequentProofNode, SequentProofNode]()

    //TODO: needs to change to e.g., [Node, Sequent]
    //so that multiple carries make sense.
    val carryMap = MMap[SequentProofNode, Sequent]()

    val carryMapList = MMap[SequentProofNode, List[Sequent]]()
    //    val replaceMap = MMap[SequentProofNode, SequentProofNode]()
    val mguMap = MMap[SequentProofNode, Substitution]()

    //    val smartCarryMap = MMap[SequentProofNode, List[(SequentProofNode, Sequent)]]()

    def addToMap(k: SequentProofNode, carry: Sequent) = {
      if (carryMap.get(k).isEmpty) {
        carryMap.put(k, carry)
      } else {
        val existingCarry = carryMap.get(k).get
        val bothCarries = existingCarry union carry
        carryMap.update(k, bothCarries)
      }
    }

    //    def addToSmartMap(k: SequentProofNode, node: SequentProofNode, carry: Sequent) = {
    //      val newPair = (node, carry)
    //      println("adding to smart map: " + newPair)
    //      val tempList = List[(SequentProofNode, Sequent)](newPair)
    //      if (smartCarryMap.get(k).isEmpty) {
    //        smartCarryMap.put(k, tempList)
    //      } else {
    //        //TODO: what if we need to update a value in an existing pair?
    //        val existingCarry = smartCarryMap.get(k).get
    //        val bothCarries = existingCarry ++ tempList
    //        smartCarryMap.update(k, bothCarries)
    //      }
    //    }

    //    def getFromSmartMap(k: SequentProofNode, node: SequentProofNode): Sequent = {
    //      val pairsOption = smartCarryMap.get(k)
    //      if (pairsOption.isEmpty) {
    //        return null
    //      }
    //      val pairs = pairsOption.get
    //
    //      def findMatch(l: List[(SequentProofNode, Sequent)]): Sequent = {
    //        for (p <- l) {
    //          val n = p._1
    //          if (n.equals(node)) {
    //            return p._2
    //          }
    //        }
    //        null
    //      }
    //
    //      findMatch(pairs)
    //
    //    }

    def addCarryToMapList(k: SequentProofNode, carry: Sequent) = {
      if (carryMapList.get(k).isEmpty) {
        carryMapList.put(k, List[Sequent](carry))
      } else {
        val existingCarry = carryMapList.get(k).get
        val bothCarries = existingCarry ++ List[Sequent](carry)
        carryMapList.update(k, bothCarries)
      }
    }

    //    println("units really are: " + unitsSet)
    def visit(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
      //      println("visiting: " + node)
      lazy val fixedLeft = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;

      println("\n\nvisiting. MAP: " + carryMap)

      val fixedP = node match {
        case Axiom(conclusion) => node
        case UnifyingResolution(left, right, _, _) if unitsSet contains left => {
          println("XX unitset must have cotained one of " + left)
          println("XX leftclean:  " + node.asInstanceOf[UnifyingResolution].leftClean)
          println("XX using " + fixedRight + " for " + node.conclusion)
          //          println(fixedRight + " --r> " + node.asInstanceOf[UnifyingResolution].auxR)
          println("XX")
          //          carryMap.update(fixedRight, makeUnitSequent(left, node.asInstanceOf[UnifyingResolution].auxR))
          //          addToSmartMap(fixedRight, node, makeUnitSequent(left, node.asInstanceOf[UnifyingResolution].auxR))

          addToMap(fixedRight, makeUnitSequent(left, node.asInstanceOf[UnifyingResolution].auxR))

          println("XX - adding carry: " + node.asInstanceOf[UnifyingResolution].auxR)
          addCarryToMapList(fixedRight, makeUnitSequent(left, node.asInstanceOf[UnifyingResolution].auxR))
          val nodeMGU = node.asInstanceOf[UnifyingResolution].mgu
          println("XX - mgu: " + nodeMGU)
          mguMap.update(fixedRight, nodeMGU)
          println("adding mgu to map: " + node.asInstanceOf[UnifyingResolution].mgu + " for " + fixedRight)
          fixedRight
        }
        case UnifyingResolution(left, right, _, _) if unitsSet contains right => {
          //          println("unitset must have cotained one of " + left + " or " + right + " for " + node)
          println("YY using " + fixedLeft + " for " + node.conclusion)
          println("YY left " + left)
          val nodeLeftClean = node.asInstanceOf[UnifyingResolution].leftClean

          println("YY left clean " + nodeLeftClean)
          //          println(fixedLeft + " --l> " + node.asInstanceOf[UnifyingResolution].auxL)
          //          println("YY")
          //          carryMap.update(fixedLeft, makeUnitSequent(right, node.asInstanceOf[UnifyingResolution].auxL))

          val renamingBackward = findRenaming(nodeLeftClean.conclusion, left.conclusion)(vars)

          val auxLCarry = makeUnitSequent(right, node.asInstanceOf[UnifyingResolution].auxL)

          val fixedCarry = updateCarry(auxLCarry, renamingBackward)

          addToMap(fixedLeft, fixedCarry)
          addCarryToMapList(fixedLeft, fixedCarry)
          //          addToSmartMap(fixedLeft, node, makeUnitSequent(right, node.asInstanceOf[UnifyingResolution].auxL))
          val nodeMGU = node.asInstanceOf[UnifyingResolution].mgu

          val fixedMGU = getRenamedMGU(left.conclusion, nodeLeftClean.conclusion, nodeMGU, vars)
          println("YY: testmgu: " + fixedMGU)

          mguMap.update(fixedLeft, fixedMGU)

          println("adding mgu to map: " + fixedMGU + " for " + fixedLeft)
          fixedLeft
        }
        //Need MRR since we might have to contract, in order to avoid ambiguous resolution
        case UnifyingResolution(left, right, _, _) => {
          //          println("attempting to resolve the following:")
          //          println(node.conclusion)

          println("caught for " + node)
          println("fixed left: " + fixedLeft)
          println("fixed right: " + fixedRight)
          println(" (l: " + left + ")")
          println(" (r: " + right + ")")
          println(" (lc: " + node.asInstanceOf[UnifyingResolution].leftClean)
          //                  println("mgu: " + node.asInstanceOf[UnifyingResolution].mgu)
          //          fixedLeft.e
          try {
            //TODO: in this case, we're not updating carries or mgus. I think this is the problem
            println("IT IS HERE?" + vars)
            val outMRR = if (fixedLeft.equals(left) && fixedRight.equals(right)) {
              println("case a")
              val outMRRa = UnifyingResolutionMRR(fixedLeft, fixedRight, node.conclusion)(vars)
              println(findRenaming(outMRRa.conclusion, node.conclusion)(vars))
              mguMap.update(outMRRa, node.asInstanceOf[UnifyingResolution].mgu)
              outMRRa
            } else {
              println("case b")

              println("case b - left: " + node.asInstanceOf[UnifyingResolution].leftPremise)
              println("case b - right: " + node.asInstanceOf[UnifyingResolution].rightPremise)
              println("case b - leftClean: " + node.asInstanceOf[UnifyingResolution].leftClean)

              val olderA = if (!mguMap.get(fixedRight).isEmpty) {
                println("case b - olderA: " + mguMap.get(fixedRight).get)
                mguMap.get(fixedRight).get
              } else { null }

              val olderB = if (!mguMap.get(fixedLeft).isEmpty) {
                println("case b - olderB: " + mguMap.get(fixedLeft).get)
                mguMap.get(fixedLeft).get
              } else { null }

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

              //TODO clear this when repairs are done
              //NOTE on this commit (or whichever is the first in which new fixed right/left are first introduced
              //the number of errors goes from 18 to 21
              //but I think the 'new fixed' gives more flexibility for repairs

              println("case b - newfixedleft: " + newFixedLeft)
              println("case b - newfixedRight: " + newFixedRight)

              //              var urMRRout = UnifyingResolutionMRR(newFixedLeft, newFixedRight)(vars)
              //this doesn't seem to help anything
              var urMRRout = try {
                UnifyingResolutionMRR(newFixedLeft, newFixedRight)(vars)
              } catch {
                case e: MRRException if (e.getMessage != null && e.getMessage.equals("Resolution (MRR): the conclusions of the given premises are not resolvable.")) => {
                  UnifyingResolutionMRR(newFixedRight, newFixedLeft)(vars)
                }
              }

              //              val urMRRout = UnifyingResolutionMRR(fixedLeft, fixedRight)(vars)
              var temp = urMRRout
              while (temp.isInstanceOf[Contraction]) {
                temp = temp.asInstanceOf[Contraction].premise
              }

              urMRRout = temp //TODO: this line introduces 2 errors. which is better?

              val carryA = if (!carryMap.get(fixedRight).isEmpty && !fixedRight.equals(right)) {
                println("case b - carry found! (right)" + carryMap.get(fixedRight).get)
                carryMap.get(fixedRight).get

              } else { null }

              //              println("case b - other carry right " + getFromSmartMap(fixedRight, right))
              //              println("case b - other carry left " + getFromSmartMap(fixedLeft, left))

              val carryB = if (!carryMap.get(fixedLeft).isEmpty && !fixedLeft.equals(left)) {
                println("case b - carry found! (left)" + carryMap.get(fixedLeft).get)
                carryMap.get(fixedLeft).get
              } else { null }

              println("case b - before contraction: " + temp.asInstanceOf[UnifyingResolution].conclusion)
              println("case b - left clean after res: " + temp.asInstanceOf[UnifyingResolution].leftClean)

              println("case b - final out " + urMRRout)
              println("case b - sub added: " + temp.asInstanceOf[UnifyingResolution].mgu)
              mguMap.update(urMRRout, temp.asInstanceOf[UnifyingResolution].mgu)

              val (leftMGU, rightMGU) = splitMGU(temp, newFixedLeft, newFixedRight)

              val updatedCarryA = updateCarry(carryA, olderA)
              val updatedCarryB = updateCarry(carryB, olderB)

              val finalUpdatedCarryA = updateCarry(updatedCarryA, rightMGU)
              val finalUpdatedCarryB = updateCarry(updatedCarryB, leftMGU)

              //              val mergedCarry = unionSequents(carryB, carryA) //21 errors
              val mergedCarry = unionSequents(finalUpdatedCarryB, finalUpdatedCarryA) //17 errors!

              //TODO: clean this up?
              val testCarry = if (mergedCarry != null) {
                val testAnt = if (mergedCarry.ant != null) {
                  mergedCarry.ant
                } else {
                  Seq[E]()
                }
                val testSuc = if (mergedCarry.suc != null) {
                  mergedCarry.suc
                } else {
                  Seq[E]()
                }
                addAntecedents(testAnt.toList) union addSuccedents(testSuc.toList)
              } else {
                null
              }

              //TODO: update both maps
              if (testCarry != null) {
                println("case b - updating carry: " + testCarry)
                //                carryMap.update(urMRRout, testCarry)
                addToMap(urMRRout, testCarry)
                //                addToSmartMap(urMRRout, node, testCarry)
              }

              urMRRout
            }
            outMRR
            //            UnifyingResolutionMRR(fixedLeft, fixedRight)(vars)
          } catch {
            case e: Exception => {
              if (e.getMessage != null) {
                if (e.getMessage.equals("Resolution (MRR): the resolvent is ambiguous.")) {

                  if (desiredFound(fixedLeft.conclusion, left.conclusion)(vars) &&
                    desiredFound(fixedRight.conclusion, right.conclusion)(vars)) {
                    //TODO: update maps in this case?
                    return UnifyingResolutionMRR(fixedLeft, fixedRight, node.conclusion)(vars)
                  }

                  //
                  //                  println("nc: " + node.conclusion)

                  //                  val oAuxL = node.asInstanceOf[UnifyingResolution].auxL
                  //                  val oAuxR = node.asInstanceOf[UnifyingResolution].auxR
                  //                  println("auxL: " + oAuxL)
                  //                  println("auxR: " + oAuxR)
                  val oMGU = node.asInstanceOf[UnifyingResolution].mgu
                  //                  println("omgu: " + oMGU)

                  //                  val oldLeftClean = node.asInstanceOf[UnifyingResolution].leftClean
                  //                  val cleanMGU = findRenaming(left.conclusion, oldLeftClean.conclusion)(vars)
                  //                  println("oldLeftClean.conclusion " + oldLeftClean.conclusion)
                  //                  println("left.conclusion " + left.conclusion)
                  //                  println("cleanMGU?? " + cleanMGU)
                  println(" caught -- cmap: " + carryMap)
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

                  var newGoalIfDesperate = null.asInstanceOf[Sequent]

                  val out = try {
                    UnifyingResolutionMRR(newFixedLeft, newFixedRight, newGoalD)(vars)
                  } catch {
                    case e: Exception => {
                      println("desperate... " + e.getMessage())
                      //                      UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalD)(vars)

                      //this one never really worked. But it's a thought? Probably safe to delete.
                      //                                            UnifyingResolutionMRR(newFixedRight, newFixedLeft, newGoalD)(vars)

                      val triedAll = tryToResolveUsingAllCarrys(node, left, right, fixedLeft, fixedRight, carryMapList, mguMap, vars)
                      val carriesOut = if (triedAll._1 == null) {
                        val triedCon = tryToResolveUsingAllCarrysAndContraction(node, left, right, fixedLeft, fixedRight, carryMapList, mguMap, vars)
                        newGoalIfDesperate = triedCon._2
                        triedCon._1
                      } else {
                        newGoalIfDesperate = triedAll._2
                        triedAll._1
                      }
                      println("reversing?")
                      tryReversingArguments(newFixedLeft, newFixedRight, newGoalD, vars)

                      carriesOut
                      //                      newGoalIfDesperate = triedAll._2
                      //                      triedAll._1
                    }
                  }

                  //                    println("made it..")

                  //                    val out = UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalD)(vars)

                  var outAfterContraction = out
                  val outContracted = Contraction(out)(vars)
                  val newSize = (outContracted.conclusion.ant.size + outContracted.conclusion.suc.size)
                  val oldSize = (out.conclusion.ant.size + out.conclusion.suc.size)
                  var contracted = false
                  if (newSize < oldSize) {
                    outAfterContraction = outContracted
                    contracted = true
                  }

                  println("out: " + out.conclusion)
                  println("ouc: " + outAfterContraction.conclusion)
                  println("newgoal: " + newGoalD)

                  val contractedGoal = if (!contracted) {
                    if (newGoalIfDesperate == null) {
                      newGoalD
                    } else {
                      newGoalIfDesperate
                    }
                  } else {
                    if (newGoalIfDesperate == null) {
                      println("-")
                      Contraction(Axiom(out.conclusion))(vars).conclusion
                    } else {
                      println("+")
                      Contraction(Axiom(newGoalIfDesperate))(vars).conclusion
                    }
                  }
                  println(" --- " + contractedGoal)

                  println("FINAL COMPUTED: " + out.conclusion)

                  println("3:" + stuff._3)
                  println("4:" + stuff._4)

                  val mergedCarry = unionSequents(stuff._3, stuff._4)

                  //                  val oldLeftClean = node.asInstanceOf[UnifyingResolution].leftClean

                  //this one, if not using new goal from trying all carries
                  //                  val cleanMGU = findRenaming(newGoalD, out.conclusion)(vars)

                  //TODO: if using all carries method, check that the maps are not trashed. 
                  //Or the merged carries for this new node. Etc.

                  val cleanMGU = if (newGoalIfDesperate == null) {
                    findRenaming(newGoalD, out.conclusion)(vars)
                    //                    findRenaming(contractedGoal, outAfterContraction.conclusion)(vars)

                  } else {
                    findRenaming(newGoalIfDesperate, out.conclusion)(vars)
                    //                    findRenaming(contractedGoal, outAfterContraction.conclusion)(vars)

                  }

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

                  //                  addToSmartMap(out, node, testCarry)
                  addCarryToMapList(out, testCarry)

                  //                  carryMap.update(out, testCarry)
                  addToMap(out, testCarry)

                  //                  carryMap.update(outAfterContraction, testCarry)
                  //                  addCarryToMapList(outAfterContraction, testCarry)
                  println("CM: after: " + carryMap)
                  //                  carryMap.update(out, mergedCarry)

                  //                  println("OUTMGU: " + out.asInstanceOf[UnifyingResolutionMRR].mgu)
                  println("BUT SAID: " + stuff._2)
                  //                  mguMap.update(outAfterContraction, stuff._2)
                  mguMap.update(out, stuff._2)

                  out
                  //                  outAfterContraction

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

  //
  def tryToResolveUsingAllCarrys(node: SequentProofNode, left: SequentProofNode, right: SequentProofNode, fixedLeft: SequentProofNode, fixedRight: SequentProofNode, carryMap: MMap[SequentProofNode, List[Sequent]], mguMap: MMap[SequentProofNode, Substitution], vars: MSet[Var]): (SequentProofNode, Sequent) = {

    println("Trying all.")

    val leftCarryList = if (!carryMap.get(fixedLeft).isEmpty) {
      carryMap.get(fixedLeft).get
    } else {
      List[Sequent]()
    }

    val rightCarryList = if (!carryMap.get(fixedRight).isEmpty) {
      carryMap.get(fixedRight).get
    } else {
      List[Sequent]()
    }

    val finalLeftCarries = (leftCarryList ++ List[Sequent](null.asInstanceOf[Sequent]))
    val finalRightCarries = (rightCarryList ++ List[Sequent](null.asInstanceOf[Sequent]))

    var finalOut = null.asInstanceOf[SequentProofNode]
    var finalGoal = null.asInstanceOf[Sequent]

    for (leftCarry <- finalLeftCarries) {
      for (rightCarry <- finalRightCarries) {
        if (finalOut == null) {
          try {

            println("checking the following left carry: " + leftCarry)
            println("checking the following right carry: " + rightCarry)
            //          val oAuxL = node.asInstanceOf[UnifyingResolution].auxL
            //          val oAuxR = node.asInstanceOf[UnifyingResolution].auxR
            //                  println("auxL: " + oAuxL)
            //                  println("auxR: " + oAuxR)
            val oMGU = node.asInstanceOf[UnifyingResolution].mgu
            //                  println("omgu: " + oMGU)

            //                  val oldLeftClean = node.asInstanceOf[UnifyingResolution].leftClean
            //                  val cleanMGU = findRenaming(left.conclusion, oldLeftClean.conclusion)(vars)
            //                  println("oldLeftClean.conclusion " + oldLeftClean.conclusion)
            //                  println("left.conclusion " + left.conclusion)
            //                  println("cleanMGU?? " + cleanMGU)
            //                  println("cma[p: " + carryMap)

            //TODO: update these, and cycle through the carries
            val carryA = if (!fixedRight.equals(right)) {
              rightCarry
            } else { null }

            val carryB = if (!fixedLeft.equals(left)) {
              leftCarry
            } else { null }

            //                  println("carry (right): " + carryA)
            //                  println("carry (left ): " + carryB)

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
            //                  println("FINAL newGoalD: " + newGoalD)

            //                  println("newFixedRight: " + newFixedRight)
            //                  println("newFixedLeft: " + newFixedLeft)

            val out = UnifyingResolutionMRR(newFixedLeft, newFixedRight, newGoalD)(vars)

            //                    println("made it..")

            //                    val out = UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalD)(vars)
            //                  println("FINAL COMPUTED: " + out.conclusion)

            //                  println("3:" + stuff._3)
            //                  println("4:" + stuff._4)

            val mergedCarry = unionSequents(stuff._3, stuff._4)

            //                  val oldLeftClean = node.asInstanceOf[UnifyingResolution].leftClean
            val cleanMGU = findRenaming(newGoalD, out.conclusion)(vars)
            //                  println("newGoalD " + newGoalD)
            //                  println("out.conclusion " + out.conclusion)
            //                  println("cleanMGU?? " + cleanMGU)

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
            //                  println("merged: " + mergedCarry)
            //                  println("test: " + testCarry)

            //                  println("putting " + testCarry + " on the map for " + out)
            //                  println("CM: before: " + carryMap)

            //TODO: add this!
            //                  addCarryToMapList(out, testCarry)

            //                  println("CM: after: " + carryMap)
            //                  carryMap.update(out, mergedCarry)

            //                  println("OUTMGU: " + out.asInstanceOf[UnifyingResolutionMRR].mgu)
            //                  println("BUT SAID: " + stuff._2)
            mguMap.update(out, stuff._2)
            println("LOOP ITERATION SUCCESFUL")

            if (finalOut == null) {
              finalOut = out
              finalGoal = newGoalD
            }

          } catch {
            case e: Exception => {
              println("Desperate attempt failed. Moving on...")
            }
          }
        }
      }
    }
    (finalOut, finalGoal)
  }

  def tryToResolveUsingAllCarrysAndContraction(node: SequentProofNode, left: SequentProofNode, right: SequentProofNode, fixedLeft: SequentProofNode, fixedRight: SequentProofNode, carryMap: MMap[SequentProofNode, List[Sequent]], mguMap: MMap[SequentProofNode, Substitution], vars: MSet[Var]): (SequentProofNode, Sequent) = {

    println("Trying all.")

    val leftCarryList = if (!carryMap.get(fixedLeft).isEmpty) {
      carryMap.get(fixedLeft).get
    } else {
      List[Sequent]()
    }

    val rightCarryList = if (!carryMap.get(fixedRight).isEmpty) {
      carryMap.get(fixedRight).get
    } else {
      List[Sequent]()
    }

    val finalLeftCarries = (leftCarryList ++ List[Sequent](null.asInstanceOf[Sequent]))
    val finalRightCarries = (rightCarryList ++ List[Sequent](null.asInstanceOf[Sequent]))

    var finalOut = null.asInstanceOf[SequentProofNode]
    var finalGoal = null.asInstanceOf[Sequent]

    for (leftCarry <- finalLeftCarries) {
      for (rightCarry <- finalRightCarries) {
        try {
          println("checking the following left carry: " + leftCarry)
          println("checking the following right carry: " + rightCarry)
          val oMGU = node.asInstanceOf[UnifyingResolution].mgu

          val carryA = if (!fixedRight.equals(right)) {
            rightCarry
          } else { null }

          val carryB = if (!fixedLeft.equals(left)) {
            leftCarry
          } else { null }

          val olderA = if (!mguMap.get(fixedRight).isEmpty) {
            mguMap.get(fixedRight).get
          } else { null }

          val olderB = if (!mguMap.get(fixedLeft).isEmpty) {
            mguMap.get(fixedLeft).get
          } else { null }

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

          val stuff = test5(fixedLeft, fixedRight, carryA, carryB, olderA, olderB, node.conclusion, oMGU, node, leftMGU, rightMGU)(vars)

          val newGoalD = stuff._1

          val contractedNewLeft = Contraction(fixedLeft)(vars)
          val contractedNewRight = Contraction(fixedRight)(vars)

          val out = UnifyingResolutionMRR(contractedNewLeft, contractedNewRight, newGoalD)(vars)

          val mergedCarry = unionSequents(stuff._3, stuff._4)

          val cleanMGU = findRenaming(newGoalD, out.conclusion)(vars)

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

          mguMap.update(out, stuff._2)
          println("LOOP ITERATION SUCCESFUL")

          if (finalOut == null) {
            finalOut = out
            finalGoal = newGoalD
          }

        } catch {
          case e: Exception => {
            println("Desperate attempt failed. Moving on...")
          }
        }
      }
    }
    (finalOut, finalGoal)
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

    //    println(lSubOut)
    //    println(rSubOut)

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

  def findUnitInSeq(node: SequentProofNode, units: List[SequentProofNode], vars: MSet[Var]): SequentProofNode = {
    if (units.size < 1) {
      return null
    } else {
      val unitToTest = units.head
      if (unitToTest.conclusion.suc.size > 0) {
        val unitFormulas = findUnifiableFormula(unitToTest.conclusion.suc.head, node.conclusion.suc)(vars)
        if (unitFormulas.size > 0) {
          unitToTest
        } else {
          findUnitInSeq(node, units.tail, vars)
        }
      } else {
        val unitFormulas = findUnifiableFormula(unitToTest.conclusion.suc.head, node.conclusion.suc)(vars)
        if (unitFormulas.size > 0) {
          unitToTest
        } else {
          findUnitInSeq(node, units.tail, vars)
        }
      }
    }
  }

  def smartContraction(left: SequentProofNode, right: SequentProofNode, units: List[SequentProofNode], vars: MSet[Var]) = {
    val newRight = Contraction(right)(vars)

    val rightsUnit = findUnitInSeq(newRight, units, vars)
    
    val rightUnitIsAnt = if (rightsUnit.conclusion.suc.size > 0) {
      false
    } else {
      true
    }
    
    val newLeftFormulas = if(!rightUnitIsAnt) {
      findUnifiableFormula(rightsUnit.conclusion.suc.head, left.conclusion.ant)(vars)
    } else {
      findUnifiableFormula(rightsUnit.conclusion.ant.head, left.conclusion.suc)(vars)
    }

    val newLeftSequent = if(rightUnitIsAnt) {
      addSuccedents(newLeftFormulas.toList)
    } else {
      addAntecedents(newLeftFormulas.toList)
    }
    
    println("NLS: " + newLeftSequent)
    
  }

  def contractAndUnify(left: SequentProofNode, right: SequentProofNode, vars: MSet[Var], units: List[SequentProofNode]) = {
    println("c and u")
    println("l: " + left)
    println("r: " + right)
    if (isUnitClause(left.conclusion)) {
      if (isUnitClause(right.conclusion)) {
        println("A")
        //Both units; no need to contract either
        UnifyingResolution(left, right)(vars)

      } else {
        println("B")
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
        println("C")

        //only left is non-unit
        val contracted = Contraction(left)(vars)
        if (contracted.conclusion.logicalSize < left.conclusion.logicalSize) {
          finishResolution(contracted, right, false)(vars)
        } else {
          finishResolution(left, right, false)(vars)

        }
      } else {
        //both are non-units
        println("D")

        val contractedL = Contraction(left)(vars)
        val contractedR = Contraction(right)(vars)
        println("CL: " + contractedL)
        println("CR: " + contractedR)
smartContraction(left, right, units, vars)
        UnifyingResolution(contractedL, contractedR)(vars)
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

        val listOfThingsToRemove = findUnifiableFormula(leftUnit, right.conclusion.ant)
        if (listOfThingsToRemove.size < 1) {
          return right
        }
        val toRemove = listOfThingsToRemove.head

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

        val listOfThingsToRemove = findUnifiableFormula(leftUnit, right.conclusion.suc)
        if (listOfThingsToRemove.size < 1) {
          return right
        }
        val toRemove = listOfThingsToRemove.head

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

        val listOfThingsToRemove = findUnifiableFormula(rightUnit, left.conclusion.ant)
        if (listOfThingsToRemove.size < 1) {
          return left
        }
        val toRemove = listOfThingsToRemove.head

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

        val listOfThingsToRemove = findUnifiableFormula(rightUnit, left.conclusion.suc)
        if (listOfThingsToRemove.size < 1) {
          return left
        }
        val toRemove = listOfThingsToRemove.head

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
    val varsC = collected._2

    println("lowerable units are: " + units)

    if (units.length == 0) {
      return proof
    }

    val fixMap = fixProofNodes(units.toSet, proof, varsC)

    def placeLoweredResolution(leftN: SequentProofNode, rightN: SequentProofNode) = {
      //      println("left: " + left)
      //      println("right: " + right)
      try {
        contractAndUnify(leftN, rightN, varsC, units)
      } catch {
        case e: Exception => {
          e.printStackTrace()

          contractAndUnify(rightN, leftN, varsC, units)
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
