package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.CanRenameVariables
import at.logic.skeptik.judgment.immutable.{ SeqSequent => Sequent }
import collection.mutable.{ Queue, HashMap => MMap }
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.expression._
import collection.mutable.{ HashSet => MSet }
import at.logic.skeptik.algorithm.unifier.{ MartelliMontanari => unify }

object FOLowerUnits
  extends (Proof[SequentProofNode] => Proof[SequentProofNode]) with CanRenameVariables {

  def isUnitClause(s: Sequent) = s.ant.length + s.suc.length == 1

  // ToDo: optimize this by interlacing collectUnits and fixProofNodes

  //I think this method is okay with FOL proofs (nothing changes),
  //but somewhere after this is called we should check the unifiability constraints?
  //or in here as we collect them?
  private def collectUnits(proof: Proof[SequentProofNode]) = {
    var vars = MSet[Var]()
    val unitsList = (proof :\ (Nil: List[SequentProofNode])) { (node, acc) =>
      if (isUnitClause(node.conclusion) && proof.childrenOf(node).length > 1) {
        println("unit: " + node)
        val children = proof.childrenOf(node)
        //This gets the child of the unit, but really we want the other parent of the child of the unit.
        val childrenConclusionsSeq = for(c <- children) yield {
          
          vars = vars union getSetOfVars(c)
          println("c: " + c)
          println("c's important stuff? " + c.conclusion )          
          c.conclusion
        }
        vars = vars union getSetOfVars(node)        
        println(checkListUnif(childrenConclusionsSeq.toList, vars))
        if (checkListUnif(childrenConclusionsSeq.toList, vars)) {
          node :: acc
        } else {
          acc
        }
        //comment this out for new behaviour
        node :: acc
      } else {
        vars = vars union getSetOfVars(node)
        acc
      }
    }
    (unitsList, vars)
  }

  private def checkListUnifiability(list: Option[List[Sequent]], vars: MSet[Var]) = list match {
    case Some(l) => checkListUnif(l, vars)
    case None => false
  }

  private def checkListUnif(l: List[Sequent], vars: MSet[Var]): Boolean = {
    if (l.length > 1) {
      val first = l.head
      val second = l.tail.head

      if (first.logicalSize == 1 && second.logicalSize == 1) {
        if (first.ant.size == 1) {
          if (second.suc.size == 1) {
            if (first.ant.head == second.suc.head) {
              return checkListUnif(l.tail, vars)
            }
          }
        } else {
          if (second.ant.size == 1) {
            if (first.suc.size == 1) {
              if (first.suc.head == second.ant.head) {
                return checkListUnif(l.tail, vars)
              }
            }
          }
        }
      }

      def isUnifiableWrapper(p: (E, E)) ={
        isUnifiable(p)(vars)
      }
        
      val unifiablePairsA = (for (auxL <- first.ant; auxR <- second.suc) yield (auxL, auxR)).filter(isUnifiableWrapper)
      val unifiablePairsB = (for (auxL <- first.suc; auxR <- second.ant) yield (auxL, auxR)).filter(isUnifiableWrapper)

      val mguResult = unifiablePairsA.length > 0 || unifiablePairsB.length > 0 

      if (mguResult) {
        checkListUnif(l.tail, vars)
      } else {
        false
      }
    } else {
      true
    }
  }

  private def checkUnifiability(proof: Proof[SequentProofNode], vars: MSet[Var]) = {
    var premiseMap = MMap[SequentProofNode, List[Sequent]]()

    //traverse the proof &
    // collect clauses being unified against units

    def visitForUnifiability(node: SequentProofNode, fixedPremises: Seq[Any]) = node match {
      case UnifyingResolution(left, right, _, _) => processResolution(left, right, premiseMap)
      case UnifyingResolutionMRR(left, right, _, _) => processResolution(left, right, premiseMap)
      case _ => node
    }

    proof.foldDown(visitForUnifiability)

    for (k <- premiseMap.keysIterator) {
      if (!checkListUnifiability(premiseMap.get(k), vars)) {
        premiseMap.put(k, Nil)
      }
    }
    premiseMap
  }

  private def processResolution(left: SequentProofNode, right: SequentProofNode, map: MMap[SequentProofNode, List[Sequent]]) = {

    if (isUnitClause(left.conclusion) && isUnitClause(right.conclusion)) {
      //Do nothing - if both are units, they must be the same, so they would have to be resolvable.?
      //TODO: check
    } else {
      if (isUnitClause(left.conclusion)) {
        left match {
          case Axiom(c) => {
            if (map.contains(left)) {
              val otherClauses = map.get(left).get
              map.remove(left)
              map.put(left, (right.conclusion :: otherClauses).distinct)
            } else {
              map.put(left, (right.conclusion :: Nil).distinct)
            }
          }
          case _ => {
            //Do nothing
          }
        }

      }
      if (isUnitClause(right.conclusion)) {
        right match {
          case Axiom(c) => {
            if (map.contains(right)) {
              val otherClauses = map.get(right).get
              map.remove(right)
              map.put(right, (left.conclusion :: otherClauses).distinct)
            } else {
              map.put(right, (left.conclusion :: Nil).distinct)
            }
          }
          case _ => {
            //Do nothing
          }
        }
      }
    }
  }

  private def fixProofNodes(unitsSet: Set[SequentProofNode], proof: Proof[SequentProofNode], vars: MSet[Var]) = {
    val fixMap = MMap[SequentProofNode, SequentProofNode]()

    def visit(node: SequentProofNode, fixedPremises: Seq[SequentProofNode]) = {
      lazy val fixedLeft = fixedPremises.head;
      lazy val fixedRight = fixedPremises.last;

      //TODO: does this check if it is an MRR/Contraction node?
      val fixedP = node match {
        case Axiom(conclusion) => node
        case UnifyingResolution(left, right, _, _) if unitsSet contains left => fixedRight
        case UnifyingResolution(left, right, _, _) if unitsSet contains right => fixedLeft
        //Need MRR since we might have to contract, in order to avoid ambiguous resolution
        case UnifyingResolution(left, right, _, _) => UnifyingResolutionMRR(fixedLeft, fixedRight)(vars)
        case _ => {
          node
        }
      }
      if (node == proof.root || unitsSet.contains(node)) {
        //        println(node + " --- " + fixedP + " --- ")
        //        println(node == proof.root)
        fixMap.update(node, fixedP)

      }
      fixedP
    }
    proof.foldDown(visit)
    fixMap
  }

  def apply(proof: Proof[SequentProofNode]) = {
    val collected = collectUnits(proof)

    val units = collected._1
    val vars = collected._2

    val premiseMap = checkUnifiability(proof, vars)
    
    
    val toRemove = MSet[SequentProofNode]()
    for (k <- premiseMap.keysIterator) {
      println(premiseMap.get(k))
      if (premiseMap.get(k) == Nil) {
        toRemove.add(k)
      }
    }

    val unitsClean = units.filter((x: SequentProofNode) => !toRemove.contains(x))
    println(units)
    //make this change for new behaviour
//    val unitsClean = units
    
    val fixMap = fixProofNodes(unitsClean.toSet, proof, vars)

    def placeLoweredResolution(left: SequentProofNode, right: SequentProofNode) = {
      try {
        UnifyingResolution(left, right)(vars)
      } catch {
        case e: Exception => {
          try {
            UnifyingResolution(right, left)(vars)
          } catch {
            case e: Exception => {
              left
            }
          }
        }
      }
    }

    val root = unitsClean.map(fixMap).foldLeft(fixMap(proof.root))(placeLoweredResolution)

    val p = Proof(root)
    println(p)
    p
  }

}
