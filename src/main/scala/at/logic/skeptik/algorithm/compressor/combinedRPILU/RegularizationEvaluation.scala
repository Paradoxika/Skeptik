package at.logic.skeptik.algorithm.compressor
package combinedRPILU

import at.logic.skeptik.proof.ProofNodeCollection
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment._
import at.logic.skeptik.judgment.immutable.{SetSequent => IClause}
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}
import scala.collection.Map

class RegularizationInformation (val estimatedSize: Float,
                                 val estimatedGainForLeftSafeLiteral: Map[E,Float],
                                 val estimatedGainForRightSafeLiteral: Map[E,Float]) {
  def /(v: Float) = new RegularizationInformation(estimatedSize / v, estimatedGainForLeftSafeLiteral.mapValues(_/v), estimatedGainForRightSafeLiteral.mapValues(_/v))
}     
object RegularizationInformation {
  def apply() =
    new RegularizationInformation(1, Map[E,Float](), Map[E,Float]())
  def apply(estimatedSize: Float) =
    new RegularizationInformation(estimatedSize, Map[E,Float](), Map[E,Float]())
  def apply(estimatedSize: Float, estimatedGainForLeftSafeLiteral: Map[E,Float], estimatedGainForRightSafeLiteral: Map[E,Float]) =
    new RegularizationInformation(estimatedSize, estimatedGainForLeftSafeLiteral, estimatedGainForRightSafeLiteral)
}

abstract class RegularizationEvaluation
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection {

  // Collector : compute information about each node (using Eval)
  protected def collectInformationMap(nodeCollection: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation]

  // Eval : compute information about CutIC nodes
  protected def evaluateDerivation(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof], aux: E,
                         leftInfo: RegularizationInformation, rightInfo:RegularizationInformation):RegularizationInformation

  // Choice : choose between lowering and regularization
  protected def lowerInsteadOfRegularize(proof: SequentProof,
                                         currentChildrenNumber: Int,
                                         information: RegularizationInformation,
                                         safeLiterals: IClause                 ):Boolean
  
  // Main functions

  private def collect(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val units = scala.collection.mutable.Queue[SequentProof]()
    val informationMap = collectInformationMap(nodeCollection)

    def isStillUnit(p: SequentProof, safeLiterals: IClause) =
      (fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc) == 1) && {
        val currentChildrenNumber = nodeCollection.childrenOf(p).foldLeft(0) { (acc,child) =>
          if (childIsMarkedToDeleteParent(child, p, edgesToDelete)) acc else (acc + 1)
        }
        (currentChildrenNumber > 1) && (lowerInsteadOfRegularize(p, currentChildrenNumber, informationMap(p), safeLiterals))
      }

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, IClause)]) = {
      val safeLiterals = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete)
      def regularize(position: DeletedSide) = {
        edgesToDelete.update(p, position)
        (p, safeLiterals)
      }
      def lower() = {
        units.enqueue(p)
        deleteFromChildren(p, nodeCollection, edgesToDelete)
        if (fakeSize(p.conclusion.ant) == 1)
          (p, new IClause(Set(p.conclusion.ant(0)), Set[E]()))
        else
          (p, new IClause(Set[E](), Set(p.conclusion.suc(0))))
      }
      p match {
        case p if isStillUnit(p, safeLiterals) => lower()
        case CutIC(_,_,_,auxR) if safeLiterals.ant contains auxR => regularize(LeftDS)
        case CutIC(_,_,auxL,_) if safeLiterals.suc contains auxL => regularize(RightDS)
        case p => (p, safeLiterals)
      }
    }

    nodeCollection.bottomUp(visit)
    (units,edgesToDelete)
  }

  def apply(proof: SequentProof): SequentProof = {
    val nodeCollection = ProofNodeCollection(proof)
    val (units,edgesToDelete) = collect(nodeCollection)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, nodeCollection)
      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
        // Right is a unit. No choice for a pivot.
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }
}

// Collectors

trait DiscreteCollector
// Assumes a derivation with more than one child won't be regularized (probability that other children will have same safe literals = 0).
// Only evaluates units and derivation with one child.
extends RegularizationEvaluation {
  protected def collectInformationMap(nodeCollection: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation] = {
    val informationMap = MMap[SequentProof, RegularizationInformation]()
    def visit(p: SequentProof, premisesInformation: List[RegularizationInformation]) = {
      val nbChildren = nodeCollection.childrenOf(p).length
      def evaluate = p match {
        case CutIC(left, right, aux, _) => evaluateDerivation(p, nodeCollection, aux, premisesInformation(0), premisesInformation(1))
        case Axiom(_) => RegularizationInformation()
      }
      (nbChildren, fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc)) match {
        case (1,_) => evaluate
        case (0,_) => RegularizationInformation()
        case (_,1) => informationMap.update(p, evaluate) ; RegularizationInformation()
        case (_,_) => RegularizationInformation()
      }
    }
    nodeCollection.foldDown(visit)
    informationMap
  }
}

trait QuadraticCollector
// Assumes probability that other children will have same safe literals = 1 / square of the number of children.
// Slow and inneficient.
extends RegularizationEvaluation {
  protected def collectInformationMap(nodeCollection: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation] = {
    val informationMap = MMap[SequentProof, RegularizationInformation]()
    def visit(p: SequentProof, premisesInformation: List[RegularizationInformation]) = {
      val nbChildren = nodeCollection.childrenOf(p).length
      def evaluate = p match {
        case CutIC(left, right, aux, _) => evaluateDerivation(p, nodeCollection, aux, premisesInformation(0), premisesInformation(1))
        case Axiom(_) => RegularizationInformation()
      }
      (nbChildren, fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc)) match {
        case (1,_) => evaluate
        case (0,_) => RegularizationInformation()
        case (_,1) => val ret = evaluate ; informationMap.update(p, ret) ; ret / (nbChildren * nbChildren).toFloat
        case (_,_) => evaluate / (nbChildren * nbChildren).toFloat
      }
    }
    nodeCollection.foldDown(visit)
    informationMap
  }
}

// Evals

trait AddEval extends RegularizationEvaluation {
// Assumes all the possible regularizations will happen.
  private def addMap(ma: Map[E,Float], mb: Map[E,Float]):Map[E,Float] =
    ma.keys.foldLeft(mb) { (acc,k) => acc + (k -> (ma(k) + mb.getOrElse(k,0..toFloat))) }
  protected def evaluateDerivation(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof], aux: E,
                                   leftInfo: RegularizationInformation, rightInfo:RegularizationInformation):RegularizationInformation = {
    val (left,right) = (proof.premises(0), proof.premises(1))
    def evalRegularization(node: SequentProof, information: RegularizationInformation) =
      if (fakeSize(nodeCollection.childrenOf(node)) == 1) information.estimatedSize + 1..toFloat else 1..toFloat
    RegularizationInformation(
      evalRegularization(left, leftInfo) + evalRegularization(right,rightInfo) - 1..toFloat,
      addMap(leftInfo.estimatedGainForLeftSafeLiteral,  rightInfo.estimatedGainForLeftSafeLiteral)  + (aux -> evalRegularization(left, leftInfo)),
      addMap(leftInfo.estimatedGainForRightSafeLiteral, rightInfo.estimatedGainForRightSafeLiteral) + (aux -> evalRegularization(right,rightInfo))
    )
  }
}

trait MinEval extends RegularizationEvaluation {
// Assumes only the worst (non-null) regularization will happen.
  private def minMap(ma: Map[E,Float], mb: Map[E,Float]):Map[E,Float] =
    ma.keys.foldLeft(mb) { (acc,k) =>
      acc + (k -> (if ((mb contains k) && (mb(k) < ma(k))) mb(k) else ma(k)))
    }
  protected def evaluateDerivation(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof], aux: E,
                                   leftInfo: RegularizationInformation, rightInfo:RegularizationInformation):RegularizationInformation = {
    RegularizationInformation(
      leftInfo.estimatedSize + rightInfo.estimatedSize - 1..toFloat,
      minMap(leftInfo.estimatedGainForLeftSafeLiteral,  rightInfo.estimatedGainForLeftSafeLiteral)  + (aux -> leftInfo.estimatedSize),
      minMap(leftInfo.estimatedGainForRightSafeLiteral, rightInfo.estimatedGainForRightSafeLiteral) + (aux -> rightInfo.estimatedSize)
    )
  }
}

// Choices

trait RegularizeIfPossible extends RegularizationEvaluation {
// Don't lower any unit that can be regularized or whose (direct or indirect) premises can be.
  protected def lowerInsteadOfRegularize(proof: SequentProof,
                                         currentChildrenNumber: Int,
                                         information: RegularizationInformation,
                                         safeLiterals: IClause                  ):Boolean = {
    val ret = !(safeLiterals.ant.exists(information.estimatedGainForLeftSafeLiteral  contains _) ||
                safeLiterals.suc.exists(information.estimatedGainForRightSafeLiteral contains _)   )
//    println("Irregular unit " + proof.conclusion + " with " + currentChildrenNumber + " children: " + ret)
    ret
  }
}

trait MinRegularizationEvaluation
extends RegularizationEvaluation {
// Assumes that only the worst (non-null) regularization of each direct premise will happen.
  protected def lowerInsteadOfRegularizeChooseOnWeight(lowerWeight: Float, regularizationWeight: Float):Boolean

  protected def lowerInsteadOfRegularize(proof: SequentProof,
                                         currentChildrenNumber: Int,
                                         information: RegularizationInformation,
                                         safeLiterals: IClause                  ):Boolean = {
    def foldFunction(info: Map[E,Float])(acc: Float, k: E) =
      if (info contains k) {
        val nval = info(k)
        if (nval < acc || acc == 0) nval else acc
      }
      else acc
    val regularizeGain =
      safeLiterals.ant.foldLeft(0..toFloat)(foldFunction(information.estimatedGainForLeftSafeLiteral))  +
      safeLiterals.suc.foldLeft(0..toFloat)(foldFunction(information.estimatedGainForRightSafeLiteral))
//    println("Clever " + proof.conclusion + " with " + currentChildrenNumber + " children, size " +
//            information.estimatedSize + " reg " + regularizeGain)
    lowerInsteadOfRegularizeChooseOnWeight((currentChildrenNumber - 1).toFloat, regularizeGain)
  }
}

trait MinLoweringChoice extends MinRegularizationEvaluation {
// Choose to lower in case of equality.
  protected def lowerInsteadOfRegularizeChooseOnWeight(lowerWeight: Float, regularizationWeight: Float) = lowerWeight >= regularizationWeight
}

trait MinRegularizationChoice extends MinRegularizationEvaluation {
// Choose to regularize in case of equality.
  protected def lowerInsteadOfRegularizeChooseOnWeight(lowerWeight: Float, regularizationWeight: Float) = lowerWeight > regularizationWeight
}

