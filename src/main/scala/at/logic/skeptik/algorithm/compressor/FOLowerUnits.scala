package at.logic.skeptik.algorithm.compressor

import at.logic.skeptik.proof.sequent.SequentProofNode
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolution
import at.logic.skeptik.proof.sequent.resolution.UnifyingResolutionMRR
import at.logic.skeptik.proof.sequent.resolution.Contraction
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

  private def collectUnits(proof: Proof[SequentProofNode]) = {
    var vars = MSet[Var]()
    val unitsList = (proof :\ (Nil: List[SequentProofNode])) { (node, acc) =>
      if (isUnitClause(node.conclusion) && proof.childrenOf(node).length > 1) {
        val children = proof.childrenOf(node)
        //This gets the child of the unit, but really we want the other parent of the child of the unit.
        //so we do the following:
        val childrensParentsConclusionsSeqSeq = for (c <- children) yield {
          val parentsConclusions = for (p <- c.premises) yield {
            p.conclusion
          }
          vars = vars union getSetOfVars(c)
          parentsConclusions
        }
        val temp = childrensParentsConclusionsSeqSeq.flatten
        vars = vars union getSetOfVars(node)
        if (checkListUnif(childrensParentsConclusionsSeqSeq.flatten.toList, vars)) {
          node :: acc
        } else {
          acc
        }

      } else {
        vars = vars union getSetOfVars(node)
        acc
      }
    }
    (unitsList, vars)
  }

  private def checkListUnif(l: List[Sequent], vars: MSet[Var]): Boolean = {
    if (l.length > 1) {
      val first = l.head
      val second = l.tail.head

      def isUnifiableWrapper(p: (E, E)) = {
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
        case UnifyingResolution(left, right, _, _) => UnifyingResolution(fixedLeft, fixedRight)(vars)
        case _ => {
          node
        }
      }
      if (node == proof.root || unitsSet.contains(node)) {
        fixMap.update(node, fixedP)

      }
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
        UnifyingResolution(left, Contraction(right)(vars))(vars)
      }
    } else {
      if (isUnitClause(right.conclusion)) {
        //only left is non-unit
        UnifyingResolution(Contraction(left)(vars), right)(vars)
      } else {
        //both are non-units 
        //Should never happen, since we are lowering a unit.
        throw new Exception("Tried to lower a non-unit")
      }
    }
  }

  def apply(proof: Proof[SequentProofNode]) = {
    val collected = collectUnits(proof)

    val units = collected._1
    val vars = collected._2

    val fixMap = fixProofNodes(units.toSet, proof, vars)

    def placeLoweredResolution(left: SequentProofNode, right: SequentProofNode) = {
      try {
        contractAndUnify(left, right, vars)
        //UnifyingResolution(left, right)(vars)

      } catch {
        case e: Exception => {
          try {
             contractAndUnify(right, left, vars)
            //UnifyingResolution(left, right)(vars)

          } catch {
            case e: Exception => {
              left
            }
          }
        }
      }
    }

    val root = units.map(fixMap).foldLeft(fixMap(proof.root))(placeLoweredResolution)

    val p = Proof(root)
    println(p)
    p
  }

}
