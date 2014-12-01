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

    //TODO: needs to change to e.g., [Node, Sequent]
    //so that multiple carries make sense.
    val carryMap = MMap[SequentProofNode, List[E]]()
    val replaceMap = MMap[SequentProofNode, SequentProofNode]()
    val mguMap = MMap[SequentProofNode, Substitution]()

    //    println("units really are: " + unitsSet)
    def visit(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]): SequentProofNode = {
      //      println("visiting: " + node)
      lazy val fixedLeft = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;

      val fixedP = node match {
        case Axiom(conclusion) => node
        case UnifyingResolution(left, right, _, _) if unitsSet contains left => {
          //          println("unitset must have cotained one of " + left + " or " + right + " for " + node)
          println("using " + fixedRight + " for " + node.conclusion)
          println(fixedRight + " --r> " + node.asInstanceOf[UnifyingResolution].auxR)
          carryMap.update(fixedRight, List[E](node.asInstanceOf[UnifyingResolution].auxR))
          replaceMap.update(fixedRight, node)
          mguMap.update(fixedRight, node.asInstanceOf[UnifyingResolution].mgu)
          fixedRight
        }
        case UnifyingResolution(left, right, _, _) if unitsSet contains right => {
          //          println("unitset must have cotained one of " + left + " or " + right + " for " + node)
          println("using " + fixedLeft + " for " + node.conclusion)
          println(fixedLeft + " --l> " + node.asInstanceOf[UnifyingResolution].auxL)

          carryMap.update(fixedLeft, List[E](node.asInstanceOf[UnifyingResolution].auxL))
          replaceMap.update(fixedLeft, node)
          mguMap.update(fixedLeft, node.asInstanceOf[UnifyingResolution].mgu)

          fixedLeft
        }
        //Need MRR since we might have to contract, in order to avoid ambiguous resolution
        case UnifyingResolution(left, right, _, _) => {
          println("attempting to resolve the following:")
          println(node.conclusion)

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

                  println("nc: " + node.conclusion)

                  val oAuxL = node.asInstanceOf[UnifyingResolution].auxL
                  val oAuxR = node.asInstanceOf[UnifyingResolution].auxR
                  println("auxL: " + oAuxL)
                  println("auxR: " + oAuxR)
                  val oMGU = node.asInstanceOf[UnifyingResolution].mgu
                  println("omgu: " + oMGU)

                  val carryA = if (!carryMap.get(fixedRight).isEmpty && !fixedRight.equals(right)) {
                    carryMap.get(fixedRight).get.head
                  } else { null }

                  val carryB = if (!carryMap.get(fixedLeft).isEmpty && !fixedLeft.equals(left)) {
                    carryMap.get(fixedLeft).get.head
                  } else { null }

                  println("carry (right): " + carryA)
                  println("carry (left ): " + carryB)

                  val olderA = if (!mguMap.get(fixedRight).isEmpty) {
                    mguMap.get(fixedRight).get
                  } else { null }

                  val olderB = if (!mguMap.get(fixedLeft).isEmpty) {
                    mguMap.get(fixedLeft).get
                  } else { null }

                  val stuff = test2(fixedLeft, fixedRight, carryA, carryB, olderA, olderB, node.conclusion, oMGU)(vars)

                  val newGoalD = stuff._1

                  println("FINAL newGoalD: " + newGoalD)
                  val out = UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalD, stuff._2)(vars)
                  println("FINAL COMPUTED: " + out.conclusion)
                  println("final carry: " + (List[E](stuff._3) ++ List[E](stuff._4)))
                  carryMap.update(out, List[E](stuff._3) ++ List[E](stuff._4))
                  mguMap.update(out, stuff._2)
                  out

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

  def makeUnitSequent(u: SequentProofNode, c: E): Sequent = {
    if(isUnitAnt(u)){
      Sequent()(c)
    } else {
      Sequent(c)()
    }
  }
  
  def isUnitAnt(u: SequentProofNode): Boolean = {
    if(u.conclusion.ant.size > 0) {
      true
    } else if (u.conclusion.suc.size > 0) {
      false
    } else {
      throw new Exception("Unit check on non-unit node")
    }
  }
  
  def test2(fl: SequentProofNode, fr: SequentProofNode, carry: E, carryB: E, older: Substitution,
    olderB: Substitution, oldGoal: Sequent, nodeMGU: Substitution)(implicit uVars: MSet[Var]): (Sequent, Substitution, E, E) = {

    def removeOnce(s: Seq[E], e: E): Seq[E] = {
      if (s.size == 0) {
        return List[E]()
      }
      val h = s.head
      if (h.equals(e)) {
        s.tail
      } else {
        removeOnce(s.tail, e) ++ List[E](h)
      }
    }

    var newNodeA = null.asInstanceOf[SequentProofNode]
    if (carry != null) {
      val newAnt = removeOnce(fr.conclusion.ant.map(e => older(e)), older(carry))
      val newSuc = fr.conclusion.suc.map(e => older(e))
      val newSeq = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
      val newNode = Axiom(newSeq)
      newNodeA = newNode
    } else {
      newNodeA = fr
    }
    var newNodeB = null.asInstanceOf[SequentProofNode]
    if (carryB != null) {
      val newAntB = removeOnce(fl.conclusion.ant.map(e => olderB(e)), olderB(carryB))
      val newSucB = fl.conclusion.suc.map(e => olderB(e))
      val newSeqB = addAntecedents(newAntB.toList) union addSuccedents(newSucB.toList)
      newNodeB = Axiom(newSeqB)
    } else {
      newNodeB = fl
    }

    println("t2: resolution:")
    println("   " + newNodeB)
    println("   " + newNodeA)
    
    val temp = UnifyingResolution(newNodeB, newNodeA, oldGoal)
    
    val tempMGU = nodeMGU// temp.mgu
    
    //    println("TEMP: " + temp)
    //    println("TEMP MGU: " + temp.mgu )
    //    println("new goal SHOULD HAVE " + temp.mgu(older(carry)))

    val outSeq = if (carryB != null && carry != null) {
      addAntecedents((temp.conclusion.ant.toList ++ List[E](tempMGU(older(carry)))
        ++ List[E](tempMGU(olderB(carryB)))).distinct) union addSuccedents(temp.conclusion.suc.toList)
    } else if (carry == null && carryB != null) {
      addAntecedents((temp.conclusion.ant.toList
        ++ List[E](tempMGU(olderB(carryB)))).distinct) union addSuccedents(temp.conclusion.suc.toList)
    } else if (carry != null && carryB == null) {
      addAntecedents((temp.conclusion.ant.toList ++ List[E](tempMGU(older(carry)))).distinct) union addSuccedents(temp.conclusion.suc.toList)
    } else {
      addAntecedents(temp.conclusion.ant.toList ++ List[E](tempMGU(older(carry)))) union addSuccedents(temp.conclusion.suc.toList)
    }

    //    println("final? : " +  outSeq)

    var outB = null.asInstanceOf[E]
    if (carryB != null) {
      outB = tempMGU(olderB(carryB))
    }

    var outA = null.asInstanceOf[E]
    if (carry != null) {
      outA = tempMGU(older(carry))
    }

    println("t2: mgu: " + tempMGU)
    (outSeq, tempMGU, outA, outB)
  }

  def test3(fl: SequentProofNode, fr: SequentProofNode, carry: Sequent, carryB: Sequent, older: Substitution,
    olderB: Substitution, oldGoal: Sequent, nodeMGU: Substitution)(implicit uVars: MSet[Var]): (Sequent, Substitution, Sequent, Sequent) = {

    def removeOnce(s: Seq[E], e: E): Seq[E] = {
      if (s.size == 0) {
        return List[E]()
      }
      val h = s.head
      if (h.equals(e)) {
        s.tail
      } else {
        removeOnce(s.tail, e) ++ List[E](h)
      }
    }
    
    def removeHalf(original: Seq[E], toRemove: Seq[E]): Seq[E] = {
      if(toRemove == null){
        original
      }
      if(toRemove.size > 0) {
        removeHalf(removeOnce(original, toRemove.head), toRemove.tail)
      } else {
        original
      }
    }
    
    var newNodeA = null.asInstanceOf[SequentProofNode]
    if (carry != null) {
      val newAnt = removeHalf(fr.conclusion.ant.map(e => older(e)), carry.ant.map(e => older(e)))
      val newSuc = removeHalf(fr.conclusion.suc.map(e => older(e)), carry.suc.map(e => older(e)))
      val newSeq = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
      val newNode = Axiom(newSeq)
      newNodeA = newNode
    } else {
      newNodeA = fr
    }
    var newNodeB = null.asInstanceOf[SequentProofNode]
    if (carryB != null) {
      val newAntB = removeHalf(fl.conclusion.ant.map(e => olderB(e)), carryB.ant.map(e => olderB(e)))
      val newSucB = removeHalf(fl.conclusion.suc.map(e => olderB(e)), carryB.suc.map(e => olderB(e)))
      val newSeqB = addAntecedents(newAntB.toList) union addSuccedents(newSucB.toList)
      newNodeB = Axiom(newSeqB)
    } else {
      newNodeB = fl
    }

    println("t2: resolution:")
    println("   " + newNodeB)
    println("   " + newNodeA)
    
    val temp = UnifyingResolution(newNodeB, newNodeA, oldGoal)
    
    val tempMGU = nodeMGU// temp.mgu
    
    //    println("TEMP: " + temp)
    //    println("TEMP MGU: " + temp.mgu )
    //    println("new goal SHOULD HAVE " + temp.mgu(older(carry)))

    val outSeq = if (carryB != null && carry != null) {
      addAntecedents((temp.conclusion.ant.toList //++ List[E](tempMGU(older(carry)))
        ++ carry.ant.map(e => tempMGU(older(e)))
        ++ carryB.ant.map(e => tempMGU(olderB(e)) //List[E](tempMGU(olderB(carryB)))
        )).distinct) union addSuccedents(
            (temp.conclusion.suc.toList
              ++ carry.suc.map(e => tempMGU(older(e)))
        ++ carryB.suc.map(e => tempMGU(olderB(e))  )))
    } else if (carry == null && carryB != null) {
      addAntecedents((temp.conclusion.ant.toList
        ++ carryB.ant.map(e => tempMGU(olderB(e)) ).distinct)) union addSuccedents(temp.conclusion.suc.toList)
    } else if (carry != null && carryB == null) {
      addAntecedents((temp.conclusion.ant.toList ++ carry.ant.map(e => tempMGU(older(e))) ).distinct) union addSuccedents(temp.conclusion.suc.toList)
    } else {
      addAntecedents(temp.conclusion.ant.toList) union addSuccedents(temp.conclusion.suc.toList)
    }

    //    println("final? : " +  outSeq)

    var outB = null.asInstanceOf[Sequent]
    if (carryB != null) {
      val newAnt = carryB.ant.map(e => olderB(e))
      val newSuc = carryB.suc.map(e => olderB(e))
      outB = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
    }

    var outA = null.asInstanceOf[Sequent]
    if (carry != null) {
      val newAnt = carry.ant.map(e => older(e))
      val newSuc = carry.suc.map(e => older(e))
      outA = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
    }

    println("t2: mgu: " + tempMGU)
    (outSeq, tempMGU, outA, outB)
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

  def contractAndUnify(left: SequentProofNode, right: SequentProofNode, vars: MSet[Var]) = {
    if (isUnitClause(left.conclusion)) {
      if (isUnitClause(right.conclusion)) {
        //        println("A")
        //Both units; no need to contract either
        UnifyingResolution(left, right)(vars)

      } else {
        //only right is non-unit
        val contracted = Contraction(right)(vars)
        if (contracted.conclusion.logicalSize < right.conclusion.logicalSize) {
          //          println("B")
          //          UnifyingResolution(left, contracted)(vars)
          finishResolution(left, contracted, true)(vars)
        } else {
          //          println("C")
          //          UnifyingResolution(left, right)(vars)
          //          try {
          //            UnifyingResolution(left, right)(vars)
          //          } catch {
          //            case e: Exception => {
          //              multipleResolution(left, right, true)(vars)
          //            }
          //          }
          finishResolution(left, right, true)(vars)
        }
      }
    } else {
      if (isUnitClause(right.conclusion)) {
        //only left is non-unit
        val contracted = Contraction(left)(vars)
        if (contracted.conclusion.logicalSize < left.conclusion.logicalSize) {
          //          println("D")
          //          UnifyingResolution(contracted, right)(vars)
          finishResolution(contracted, right, false)(vars)
        } else {
          //          println("E")
          //          UnifyingResolution(left, right)(vars)
          finishResolution(left, right, false)(vars)

        }
      } else {
        //both are non-units
        //        println("F")
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
      println("left: " + left)
      println("right: " + right)
      try {
        //                println("A")
        contractAndUnify(left, right, vars)
      } catch {
        case e: Exception => {
          //                    println("B " + e.getMessage())
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
