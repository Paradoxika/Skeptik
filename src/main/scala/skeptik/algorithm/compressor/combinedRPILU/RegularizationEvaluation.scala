package skeptik.algorithm.compressor
package combinedRPILU

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

class RegularizationInformation (val nodeSize: Float, val leftMap: Map[E,Float], val rightMap: Map[E,Float]) {
  def /(v: Float) = new RegularizationInformation(nodeSize / v, leftMap.mapValues(_/v), rightMap.mapValues(_/v))
}     
object RegularizationInformation {
  def apply() =
    new RegularizationInformation(1, Map[E,Float](), Map[E,Float]())
  def apply(nodeSize: Float) =
    new RegularizationInformation(nodeSize, Map[E,Float](), Map[E,Float]())
  def apply(nodeSize: Float, leftMap: Map[E,Float], rightMap: Map[E,Float]) =
    new RegularizationInformation(nodeSize, leftMap, rightMap)
}

// There are many variant of this algorithm. Only some of them are instanciated in Experimenter.
// The others should probably be deleted.

abstract class RegularizationEvaluation
extends AbstractRPIAlgorithm with UnitsCollectingBeforeFixing with Intersection with LeftHeuristic {

  // Collector : compute information about each node (using Eval)
  def collectInformationMap(nodeCollection: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation]

  // Eval : compute information about CutIC nodes
  def evaluateDerivation(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof], aux: E,
                         left:  SequentProof, leftInfo: RegularizationInformation,
                         right: SequentProof, rightInfo:RegularizationInformation):RegularizationInformation

  // Choice : choose between lowering and regularization
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])         ):Boolean
  
  // Main functions

  private def collect(nodeCollection: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val units = scala.collection.mutable.Queue[SequentProof]()
    val informationMap = collectInformationMap(nodeCollection)

    def isTrueUnit(p: SequentProof, safeLiterals: (Set[E],Set[E])) =
      (fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc) == 1) && {
        val aliveChildren = nodeCollection.childrenOf(p).foldLeft(0) { (acc,child) =>
          if (childIsMarkedToDeleteParent(child, p, edgesToDelete)) acc else (acc + 1)
        }
        (aliveChildren > 1) && (lowerInsteadOfRegularize(p, aliveChildren, informationMap(p), safeLiterals))
      }

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      val (safeL,safeR) = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
      def regularize(position: DeletedSide) = {
        edgesToDelete.update(p, position)
        (p, safeL, safeR)
      }
      def lower() = {
        units.enqueue(p)
        deleteFromChildren(p, nodeCollection, edgesToDelete)
        if (fakeSize(p.conclusion.ant) == 1)
          (p, Set(p.conclusion.ant(0)), Set[E]())
        else
          (p, Set[E](), Set(p.conclusion.suc(0)))
      }
      p match {
        case p if isTrueUnit(p, (safeL,safeR)) => lower()
        case CutIC(_,_,_,auxR) if safeL contains auxR => regularize(LeftDS)
        case CutIC(_,_,auxL,_) if safeR contains auxL => regularize(RightDS)
        case p => (p, safeL, safeR)
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
  def collectInformationMap(nodeCollection: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation] = {
    var informationMap = MMap[SequentProof, RegularizationInformation]()
    def visit(p: SequentProof, premisesInformation: List[RegularizationInformation]) = {
      val nbChildren = nodeCollection.childrenOf(p).length
      def evaluate = p match {
        case CutIC(left, right, aux, _) => evaluateDerivation(p, nodeCollection, aux, left, premisesInformation(0), right, premisesInformation(1))
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
  def collectInformationMap(nodeCollection: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation] = {
    var informationMap = MMap[SequentProof, RegularizationInformation]()
    def visit(p: SequentProof, premisesInformation: List[RegularizationInformation]) = {
      val nbChildren = nodeCollection.childrenOf(p).length
      def evaluate = p match {
        case CutIC(left, right, aux, _) => evaluateDerivation(p, nodeCollection, aux, left, premisesInformation(0), right, premisesInformation(1))
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
// Assumes all the possible regularizations will happend.
  def addMap(ma: Map[E,Float], mb: Map[E,Float]):Map[E,Float] =
    ma.keys.foldLeft(mb) { (acc,k) => acc + (k -> (ma(k) + mb.getOrElse(k,0..toFloat))) }
  def evaluateDerivation(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof], aux: E,
                         left:  SequentProof, leftInfo: RegularizationInformation,
                         right: SequentProof, rightInfo:RegularizationInformation):RegularizationInformation = {
    def evalRegularization(node: SequentProof, information: RegularizationInformation) =
      if (fakeSize(nodeCollection.childrenOf(node)) == 1) information.nodeSize + 1..toFloat else 1..toFloat
    RegularizationInformation(
      evalRegularization(left, leftInfo) + evalRegularization(right,rightInfo) - 1..toFloat,
      addMap(leftInfo.leftMap,  rightInfo.leftMap)  + (aux -> evalRegularization(left, leftInfo)),
      addMap(leftInfo.rightMap, rightInfo.rightMap) + (aux -> evalRegularization(right,rightInfo))
    )
  }
}

trait MinEval extends RegularizationEvaluation {
// Assumes only the worst (non-null) regularization will happend.
  def minMap(ma: Map[E,Float], mb: Map[E,Float]):Map[E,Float] =
    ma.keys.foldLeft(mb) { (acc,k) =>
      acc + (k -> (if ((mb contains k) && (mb(k) < ma(k))) mb(k) else ma(k)))
    }
  def evaluateDerivation(proof: SequentProof, nodeCollection: ProofNodeCollection[SequentProof], aux: E,
                         left:  SequentProof, leftInfo: RegularizationInformation,
                         right: SequentProof, rightInfo:RegularizationInformation):RegularizationInformation = {
    RegularizationInformation(
      leftInfo.nodeSize + rightInfo.nodeSize - 1..toFloat,
      minMap(leftInfo.leftMap,  rightInfo.leftMap)  + (aux -> leftInfo.nodeSize),
      minMap(leftInfo.rightMap, rightInfo.rightMap) + (aux -> rightInfo.nodeSize)
    )
  }
}

// Choices

trait RegularizeIfPossible extends RegularizationEvaluation {
// Don't lower any unit that can be regularized or whose (direct or indirect) premises can be.
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])          ):Boolean = {
    val ret = !(safeLiterals._1.exists(information.leftMap  contains _) ||
      safeLiterals._2.exists(information.rightMap contains _)   )
//    println("Irregular unit " + proof.conclusion + " with " + notDeletedChildren + " children: " + ret)
    ret
  }
}

abstract class MinRegularizationEvaluation
extends RegularizationEvaluation {
// Assumes that only the worst (non-null) regularization of each direct premise will happend.
  def lowerInsteadOfRegularizeChooseOnWeight(lowerWeight: Float, regularizationWeight: Float):Boolean

  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])          ):Boolean = {
    def foldFunction(info: Map[E,Float])(acc: Float, k: E) =
      if (info contains k) {
        val nval = info(k)
        if (nval < acc || acc == 0) nval else acc
      }
      else acc
    val regularizeGain =
      safeLiterals._1.foldLeft(0..toFloat)(foldFunction(information.leftMap))  +
      safeLiterals._2.foldLeft(0..toFloat)(foldFunction(information.rightMap))
//    println("Clever " + proof.conclusion + " with " + notDeletedChildren + " children, size " +
//            information.nodeSize + " reg " + regularizeGain)
    lowerInsteadOfRegularizeChooseOnWeight((notDeletedChildren - 1).toFloat, regularizeGain)
  }
}

trait MinLoweringChoice extends MinRegularizationEvaluation {
// Choose to lower in case of equality.
  def lowerInsteadOfRegularizeChooseOnWeight(lowerWeight: Float, regularizationWeight: Float) = lowerWeight >= regularizationWeight
}

trait MinRegularizationChoice extends MinRegularizationEvaluation {
// Choose to regularize in case of equality.
  def lowerInsteadOfRegularizeChooseOnWeight(lowerWeight: Float, regularizationWeight: Float) = lowerWeight > regularizationWeight
}

