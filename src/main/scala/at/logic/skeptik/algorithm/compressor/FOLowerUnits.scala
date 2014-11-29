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
          println("using " + fixedRight + " for " + node.conclusion)
          fixedRight
        }
        case UnifyingResolution(left, right, _, _) if unitsSet contains right => {
          //          println("unitset must have cotained one of " + left + " or " + right + " for " + node)
          println("using " + fixedLeft + " for " + node.conclusion)
          fixedLeft
        }
        //Need MRR since we might have to contract, in order to avoid ambiguous resolution
        case UnifyingResolution(left, right, _, _) => {
          println("attempting to resolve the following:")
          println(node.conclusion)
          //                    println("left: " + fixedLeft + " (l: " + left + ")")
          //                    println("right: " + fixedRight + " (r: " + right + ")")
          //          println(vars)
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
                  val oMGU = node.asInstanceOf[UnifyingResolution].mgu
                  println("omgu: " + oMGU)
//                  val cb = oMGU(getCarry(right, isAntUnit(unitsSet.head)))
//                  val newGoalB = addCarry(node.conclusion, cb, unitsSet.head)
//                  println("THIS ONE: " + newGoalB)

                  val cbb = oMGU(getCarryB(right, isAntUnit(unitsSet.head)))
                  val newGoalC = addCarry(node.conclusion, cbb, unitsSet.head)
                  println("NC: " + newGoalC)
                  
                  println("ND: " + addCarry(node.conclusion, getCarryB(right, isAntUnit(unitsSet.head)), unitsSet.head))
                  
                  //                  val carry = findCorrected(node.asInstanceOf[UnifyingResolution].auxR, unitsSet.head.conclusion.suc.head,
                  //                    fixedRight, right.conclusion, true, node.asInstanceOf[UnifyingResolution].mgu)(vars)
                  println("rc: " + right.conclusion)
                  println("lc: " + left.conclusion)
                  //                  val carry = findCorrected(node.asInstanceOf[UnifyingResolution].auxL, getUnitE(unitsSet.head),
                  //                    fixedRight, right.conclusion, false, node.asInstanceOf[UnifyingResolution].mgu)(vars)
                  //                  println(carry._1)
                  //                  val newGoal = addCarry(node.conclusion, carry._1, unitsSet.head)
                  //                  println("newGoal: " + newGoal)

                  //                  findOriginal(unitsSet.head, fixedLeft, right, fixedRight, node.conclusion)(vars)

                  //                  println("success: " + UnifyingResolutionMRR(fixedLeft, fixedRight, newGoal)(vars))
                  //                  val child = flChildren.intersect(frChildren).head
                  //                  println("child: " + child)
                  //                  println("node: " + node)

                  //                  UnifyingResolutionMRR(fixedRight, fixedLeft, newGoal, carry._2)(vars)
                  //                  println("CARRY: " + carry._2)
                  
                  //TODO: make this better?
//                  try {
//                    UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalB, oMGU)(vars)
//                  } catch {
//                    case e: Exception => {
//                      println("what?")
                      UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalC, oMGU)(vars)
//                    }
//                  }
                  //                  UnifyingResolutionMRR(fixedLeft, fixedRight, newGoalB)(vars)

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

  def isAntUnit(u: SequentProofNode): Boolean = {
    if (u.conclusion.ant.size > 0) {
      true
    } else {
      false
    }
  }

  def getCarry(original: SequentProofNode, isAntUnit: Boolean) = {
    //    println("omgu: " + original.asInstanceOf[UnifyingResolution].mgu)//TODO: use this to solve it?
    println("ORIGINAL: " + original)
    val omgu = original.asInstanceOf[UnifyingResolution].mgu
    
    if (isAntUnit) {
      omgu(original.asInstanceOf[UnifyingResolution].auxL)
      //      original.asInstanceOf[UnifyingResolution].auxL
    } else {
      omgu(original.asInstanceOf[UnifyingResolution].auxR)
      //      original.asInstanceOf[UnifyingResolution].auxR
    }
  }

  def getCarryB(original: SequentProofNode, isAntUnit: Boolean) = {
    println("original in carryB: " + original)
    if (isAntUnit) {
      original.asInstanceOf[UnifyingResolution].auxL
    } else {
      original.asInstanceOf[UnifyingResolution].auxR
    }
  }

  //
  def addCarry(con: Sequent, carry: E, unit: SequentProofNode): Sequent = {
    if (unit.conclusion.ant.size > 0) {
      addAntecedents(con.ant.toList) union addSuccedents(con.suc.toList ++ List[E](carry))
    } else if (unit.conclusion.suc.size > 0) {
      addAntecedents(con.ant.toList ++ List[E](carry)) union addSuccedents(con.suc.toList)
    } else {
      null //stub; error //TODO: throw something or handle this when function called
    }
  }

  //
  def getUnitE(unit: SequentProofNode): E = {
    if (unit.conclusion.ant.size > 0) {
      unit.conclusion.ant.head
    } else if (unit.conclusion.suc.size > 0) {
      unit.conclusion.suc.head
    } else {
      null //stub //TODO: throw error?
    }
  }

  //
  def findCorrected(aux: E, unit: E, fixed: SequentProofNode, original: Sequent, auxInAnt: Boolean, mgu: Substitution)(implicit uVars: MSet[Var]): (E, Substitution) = {

    def filterFunc(expr: E)(implicit uVars: MSet[Var]): Boolean = {
      !desiredFound(Sequent(expr)(), Sequent(unit)())
    }

    def removeOnce(s: Seq[E], e: E): Seq[E] = {
      val h = s.head
      if (filterFunc(h)) {
        s.tail
      } else {
        removeOnce(s.tail, e) ++ List[E](h)
      }
    }

    if (auxInAnt) {
      for (f <- fixed.conclusion.ant) {
        val u = getUnifier((f, aux))
        if (u != null) {
          println("u a: " + u)
          //          val newAnt = removeOnce(fixed.conclusion.ant.map(e => u(e)), u(f))
          //          //fixed.conclusion.ant.map(e => u(e)).filter(filterFunc)
          //
          //          val newSuc = fixed.conclusion.suc.map(e => u(e))
          val newAnt = fixed.conclusion.ant.map(e => u(e))
          val newSuc = removeOnce(fixed.conclusion.suc.map(e => u(e)), u(f))
          val newConclusion = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
          println("o: " + original)
          println("F: " + f)
          println("new: " + newConclusion)

          if (desiredFound(newConclusion, original)) {
            return (mgu(u(f)), u)
          }
        }
      }
      null //stub; error //TODO: throw something
    } else {
      println("o: " + original)
      for (f <- fixed.conclusion.suc) {

        val u = getUnifier((f, aux))

        if (u != null) {
          println("u: " + u)
          val newAnt = fixed.conclusion.ant.map(e => u(e))
          println("B " + removeOnce(fixed.conclusion.suc.map(e => u(e)), u(f)))

          val newSuc = removeOnce(fixed.conclusion.suc.map(e => u(e)), u(f)) //fixed.conclusion.suc.map(e => u(e)).filter(filterFunc) //can't filter, must remove *one* copy
          val newConclusion = addAntecedents(newAnt.toList) union addSuccedents(newSuc.toList)
          println("new: " + newConclusion)
          if (desiredFound(newConclusion, original)) {
            println("C")
            return (mgu(u(unit)), u)
          }
        }
      }
      null //stub; error //TODO: throw something
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
