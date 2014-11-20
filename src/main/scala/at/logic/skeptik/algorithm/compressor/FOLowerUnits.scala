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

object FOLowerUnits
  extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with CanRenameVariables with FindDesiredSequent {

  def isUnitClause(s: Sequent) = s.ant.length + s.suc.length == 1

  // ToDo: optimize this by interlacing collectUnits and fixProofNodes

  def cleanUpLists(in: IndexedSeq[Seq[Seq[E]]]) = {
    var out = List[E]()
    for(outer <- in){
      for(inner <- outer){
        out = out ++ inner 
      }
    }
    
//    println("cleaned: " + out.distinct)
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
            val o = getUnitLiteral(p.conclusion, node.conclusion, vars)//
//            println("o: " + o)
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
        
       
        val listOfUnits =  cleanUpLists(childrensParentsConclusionsSeqSeq)

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
      println("visiting: " + node)
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
          println("left: " + fixedLeft + " (l: " + left + ")")
          println("right: " + fixedRight + " (r: " + right + ")")
          println(vars)
          try {
            UnifyingResolutionMRR(fixedLeft, fixedRight)(vars)
          } catch {
            case e: Exception => {
              if (e.getMessage != null) {
                if (e.getMessage.equals("Resolution (MRR): the resolvent is ambiguous.")) {
                                    println("caught")
                  //                  println(proof.childrenOf.contains(fixedLeft))
                  //                  println(proof.childrenOf.contains(fixedRight))

                  val frChildren = childrenOfFixed(proof, fixedRight, vars)
                  val flChildren = childrenOfFixed(proof, fixedLeft, vars)

                  //                  val flChildren = proof.childrenOf.get(fixedLeft).get
                  //                  val frChildren = proof.childrenOf.get(fixedRight).get
                  //                  val flChildren = proof.childrenOf.get(left).get
                  //                  val frChildren = proof.childrenOf.get(right).get 

//                  println("flC: " + flChildren)
//                  println("frC: " + frChildren)
                  val child = flChildren.intersect(frChildren).head
//                  println("child: " + child)
//                  println("node: " + node)
                  UnifyingResolutionMRR(fixedLeft, fixedRight, child.conclusion)(vars)
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
        fixMap.update(node, fixedP)
      }
//      println("node: " + node)
//      println("fixedP: " + fixedP)
      fixedP
    }
    proof.foldDown(visit)
    fixMap
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

  def apply(proof: Proof[SequentProofNode]) = {
    val collected = collectUnits(proof)

    val units = collected._1
    val vars = collected._2

    println("lowerable units are: " + units)

    val fixMap = fixProofNodes(units.toSet, proof, vars)

    def placeLoweredResolution(left: SequentProofNode, right: SequentProofNode) = {
      try {
        contractAndUnify(left, right, vars)
      } catch {
        case e: Exception => {
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
