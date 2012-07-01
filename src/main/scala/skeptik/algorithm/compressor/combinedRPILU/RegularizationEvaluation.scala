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
  def +(that: RegularizationInformation) =
    new RegularizationInformation(this.nodeSize + that.nodeSize, 
                                  RegularizationInformation.addMap(this.leftMap, that.leftMap),
                                  RegularizationInformation.addMap(this.rightMap, that.rightMap))
  def /(v: Float) = new RegularizationInformation(nodeSize / v, leftMap.mapValues(_/v), rightMap.mapValues(_/v))
}     
object RegularizationInformation {
  def addMap(ma: Map[E,Float], mb: Map[E,Float]):Map[E,Float] =
    ma.keys.foldLeft(mb) { (acc,k) => acc + (k -> (ma(k) + mb.getOrElse(k,0..toFloat))) }
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
  def collectInformationMap(iterator: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation]

  // Eval : compute information about CutIC nodes
  def evaluateDerivation(proof: SequentProof, iterator: ProofNodeCollection[SequentProof], aux: E,
                         left:  SequentProof, leftInfo: RegularizationInformation,
                         right: SequentProof, rightInfo:RegularizationInformation):RegularizationInformation

  // Choice : choose between lowering and regularization
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])         ):Boolean
  
  // Main functions

  private def collect(iterator: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val units = scala.collection.mutable.Queue[SequentProof]()
    val informationMap = collectInformationMap(iterator)

    def isTrueUnit(p: SequentProof, safeLiterals: (Set[E],Set[E])) =
      (fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc) == 1) && {
        val aliveChildren = iterator.childrenOf.getOrElse(p,Nil).foldLeft(0) { (acc,child) =>
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
        deleteFromChildren(p, iterator, edgesToDelete)
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

    iterator.bottomUp(visit)
    (units,edgesToDelete)
  }

  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val (units,edgesToDelete) = collect(iterator)
    if (edgesToDelete.isEmpty) proof else {
      val fixMap = mapFixedProofs(units.toSet + proof, edgesToDelete, iterator)
      units.map(fixMap).foldLeft(fixMap(proof)) { (left,right) =>
        try {CutIC(left,right)} catch {case e:Exception => left}
      }
    }
  }
}

// Collectors

trait SimpleCollector
// The same information is calculated and stored in the map. Every derivation is evaluated.
// This is both inefficient and error-prone.
// Should be deleted.
extends RegularizationEvaluation {
  def collectInformationMap(iterator: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation] = {
    var informationMap = MMap[SequentProof, RegularizationInformation]()
    def visit(p: SequentProof, premisesInformation: List[RegularizationInformation]) =  {
      val ret = p match {
        case CutIC(left, right, aux, _) => evaluateDerivation(p, iterator, aux, left, premisesInformation(0), right, premisesInformation(1))
        case _ => RegularizationInformation()
      }
      if (isUnit(p, iterator)) informationMap.update(p, ret)
      ret
    }
    iterator.foldDown(visit)
    informationMap
  }
}

trait DiscreteCollector
// Assumes a derivation with more than one child won't be regularized (probability that other children will have same safe literals = 0).
// Only evaluates units and derivation with one child.
// Should be kept, best collector.
extends RegularizationEvaluation {
  def collectInformationMap(iterator: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation] = {
    var informationMap = MMap[SequentProof, RegularizationInformation]()
    def visit(p: SequentProof, premisesInformation: List[RegularizationInformation]) = {
      val nbChildren = iterator.childrenOf.getOrElse(p, Nil).length
      def evaluate = p match {
        case CutIC(left, right, aux, _) => evaluateDerivation(p, iterator, aux, left, premisesInformation(0), right, premisesInformation(1))
        case Axiom(_) => RegularizationInformation()
      }
      (nbChildren, fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc)) match {
        case (1,_) => evaluate
        case (0,_) => RegularizationInformation()
        case (_,1) => informationMap.update(p, evaluate) ; RegularizationInformation()
        case (_,_) => RegularizationInformation()
      }
    }
    iterator.foldDown(visit)
    informationMap
  }
}

trait QuadraticCollector
// Assumes probability that other children will have same safe literals = 1 / square of the number of children.
// Slow and inneficient.
// Should be kept anyway because it's an interessing idea.
extends RegularizationEvaluation {
  def collectInformationMap(iterator: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation] = {
    var informationMap = MMap[SequentProof, RegularizationInformation]()
    def visit(p: SequentProof, premisesInformation: List[RegularizationInformation]) = {
      val nbChildren = iterator.childrenOf.getOrElse(p, Nil).length
      def evaluate = p match {
        case CutIC(left, right, aux, _) => evaluateDerivation(p, iterator, aux, left, premisesInformation(0), right, premisesInformation(1))
        case Axiom(_) => RegularizationInformation()
      }
      (nbChildren, fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc)) match {
        case (1,_) => evaluate
        case (0,_) => RegularizationInformation()
        case (_,1) => val ret = evaluate ; informationMap.update(p, ret) ; ret / (nbChildren * nbChildren).toFloat
        case (_,_) => evaluate / (nbChildren * nbChildren).toFloat
      }
    }
    iterator.foldDown(visit)
    informationMap
  }
}

// Evals

trait AddEval extends RegularizationEvaluation {
// Assumes all the possible regularizations will happend.
// Ineficient but should be kept.
  def evaluateDerivation(proof: SequentProof, iterator: ProofNodeCollection[SequentProof], aux: E,
                         left:  SequentProof, leftInfo: RegularizationInformation,
                         right: SequentProof, rightInfo:RegularizationInformation):RegularizationInformation = {
    def evalRegularization(node: SequentProof, information: RegularizationInformation) =
      if (fakeSize(iterator.childrenOf.getOrElse(node,Nil)) == 1) information.nodeSize + 1..toFloat else 1..toFloat
    RegularizationInformation(
      evalRegularization(left, leftInfo) + evalRegularization(right,rightInfo) - 1..toFloat,
      RegularizationInformation.addMap(leftInfo.leftMap,  rightInfo.leftMap)  + (aux -> evalRegularization(left, leftInfo)),
      RegularizationInformation.addMap(leftInfo.rightMap, rightInfo.rightMap) + (aux -> evalRegularization(right,rightInfo))
    )
  }
}

trait MaxEval extends RegularizationEvaluation {
// Assumes only the best regularization will happend.
// Should be deleted because it's ineficient, theoretically wrong and because OptimizedEval does it better.
  def maxMap(ma: Map[E,Float], mb: Map[E,Float]):Map[E,Float] =
    ma.keys.foldLeft(mb) { (acc,k) =>
      acc + (k -> (if ((mb contains k) && (mb(k) > ma(k))) mb(k) else ma(k)))
    }
  def evaluateDerivation(proof: SequentProof, iterator: ProofNodeCollection[SequentProof], aux: E,
                         left:  SequentProof, leftInfo: RegularizationInformation,
                         right: SequentProof, rightInfo:RegularizationInformation):RegularizationInformation = {
    def evalRegularization(node: SequentProof, information: RegularizationInformation) =
      if (fakeSize(iterator.childrenOf.getOrElse(node,Nil)) == 1) information.nodeSize + 1..toFloat else 1..toFloat
    RegularizationInformation(
      evalRegularization(left, leftInfo) + evalRegularization(right, rightInfo) - 1..toFloat,
      maxMap(leftInfo.leftMap,  rightInfo.leftMap)  + (aux -> evalRegularization(left, leftInfo)),
      maxMap(leftInfo.rightMap, rightInfo.rightMap) + (aux -> evalRegularization(right,rightInfo))
    )
  }
}

trait OptimizedEval extends RegularizationEvaluation {
// Same as MaxEval, but optimized to be used with DiscreteCollector.
// May be deleted as it's theoretically wrong.
  def maxMap(ma: Map[E,Float], mb: Map[E,Float]):Map[E,Float] =
    ma.keys.foldLeft(mb) { (acc,k) =>
      acc + (k -> (if ((mb contains k) && (mb(k) > ma(k))) mb(k) else ma(k)))
    }
  def evaluateDerivation(proof: SequentProof, iterator: ProofNodeCollection[SequentProof], aux: E,
                         left:  SequentProof, leftInfo: RegularizationInformation,
                         right: SequentProof, rightInfo:RegularizationInformation):RegularizationInformation = {
    RegularizationInformation(
      leftInfo.nodeSize + rightInfo.nodeSize - 1..toFloat,
      maxMap(leftInfo.leftMap,  rightInfo.leftMap)  + (aux -> leftInfo.nodeSize),
      maxMap(leftInfo.rightMap, rightInfo.rightMap) + (aux -> rightInfo.nodeSize)
    )
  }
}

trait MinEval extends RegularizationEvaluation {
// Assumes only the worst (non-null) regularization will happend.
// Gives the same results as OptimizedEval but is more correct as it can really compute the bare minimum gain due to regularization.
// Sould be kept.
  def minMap(ma: Map[E,Float], mb: Map[E,Float]):Map[E,Float] =
    ma.keys.foldLeft(mb) { (acc,k) =>
      acc + (k -> (if ((mb contains k) && (mb(k) < ma(k))) mb(k) else ma(k)))
    }
  def evaluateDerivation(proof: SequentProof, iterator: ProofNodeCollection[SequentProof], aux: E,
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

trait AlwaysLowerI extends RegularizationEvaluation {
// Should be deleted as it gives the same results as AlwaysLowerIrregularUnits but is much slower.
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])         ):Boolean = true
}

trait AlwaysRegularizeI extends RegularizationEvaluation {
// Don't lower any unit that can be regularized or whose (direct or indirect) premises can be.
// Should be kept (but renamed).
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

abstract class MaxChoice (deletionProbability: Double)
// Assumes that only the best regularization will happend and that lowered units have deletionProbability to be deleted.
// Experiments shows that deletionProbability (and then nodeSize) is useless.
// Should be deleted because assumptions are wrong.
extends RegularizationEvaluation {
  def max(x: Float, y: Float) = if (x < y) y else x
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])          ):Boolean = {
    val regularizeGain = max(
      safeLiterals._1.foldLeft(0..toFloat) { (acc,k) => max(acc, information.leftMap.getOrElse(k,0..toFloat))  },
      safeLiterals._2.foldLeft(0..toFloat) { (acc,k) => max(acc, information.rightMap.getOrElse(k,0..toFloat)) })
//    println("Clever " + proof.conclusion + " with " + notDeletedChildren + " children, size " +
//            information.nodeSize + " reg " + regularizeGain)
    (notDeletedChildren - 1).toFloat + (information.nodeSize * deletionProbability) > regularizeGain
  }
}

abstract class AddChoice (deletionProbability: Double)
// Assumes that all possible regularizations will happend and that lowered unit has deletionProbability to be deleted.
// Should be deleted because assumptions are wrong.
extends RegularizationEvaluation {
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])          ):Boolean = {
    val regularizeGain =
      safeLiterals._1.foldLeft(0..toFloat) { (acc,k) => acc + information.leftMap.getOrElse(k,0..toFloat)  } +
      safeLiterals._2.foldLeft(0..toFloat) { (acc,k) => acc + information.rightMap.getOrElse(k,0..toFloat) }
//    println("Clever " + proof.conclusion + " with " + notDeletedChildren + " children, size " +
//            information.nodeSize + " reg " + regularizeGain)
    (notDeletedChildren - 1).toFloat + (information.nodeSize * deletionProbability) > regularizeGain
  }
}

abstract class MixChoice (deletionProbability: Double)
// Assumes that only the best regularization of each direct premise will happend and that lowered unit has deletionProbability to be deleted.
// Should be deleted because assumptions are wrong. But may be kept if OptimizedEval is kept.
extends RegularizationEvaluation {
  def max(x: Float, y: Float) = if (x < y) y else x
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])          ):Boolean = {
    val regularizeGain =
      safeLiterals._1.foldLeft(0..toFloat) { (acc,k) => max(acc, information.leftMap.getOrElse(k,0..toFloat))  } +
      safeLiterals._2.foldLeft(0..toFloat) { (acc,k) => max(acc, information.rightMap.getOrElse(k,0..toFloat)) }
//    println("Clever " + proof.conclusion + " with " + notDeletedChildren + " children, size " +
//            information.nodeSize + " reg " + regularizeGain)
    (notDeletedChildren - 1).toFloat + (information.nodeSize * deletionProbability) > regularizeGain
  }
}

abstract class MixMinChoice (deletionProbability: Double)
// Assumes that only the worst regularization of each direct premise will happend and that lowered unit has deletionProbability to be deleted.
// Should be deleted because deletionProbability (and then nodeSize) is useless.
extends RegularizationEvaluation {
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
    (notDeletedChildren - 1).toFloat + (information.nodeSize * deletionProbability) > regularizeGain
  }
}

trait OptimizedLoweringChoice extends RegularizationEvaluation {
// Assumes that only the best regularization of each direct premise will happend.
// Choose to lower in case of equality.
// Shoudl be kept (but renamed) if OptimizedEval is kept, deleted otherwise.
  def max(x: Float, y: Float) = if (x < y) y else x
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])          ):Boolean = {
    val regularizeGain =
      safeLiterals._1.foldLeft(0..toFloat) { (acc,k) => max(acc, information.leftMap.getOrElse(k,0..toFloat))  } +
      safeLiterals._2.foldLeft(0..toFloat) { (acc,k) => max(acc, information.rightMap.getOrElse(k,0..toFloat)) }
//    println("Clever " + proof.conclusion + " with " + notDeletedChildren + " children, size " +
//            information.nodeSize + " reg " + regularizeGain)
    (notDeletedChildren - 1).toFloat >= regularizeGain
  }
}

trait OptimizedRegularizationChoice extends RegularizationEvaluation {
// Assumes that only the best regularization of each direct premise will happend.
// Choose to regularize in case of equality.
// Shoudl be kept (but renamed) if OptimizedEval is kept, deleted otherwise.
  def max(x: Float, y: Float) = if (x < y) y else x
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])          ):Boolean = {
    val regularizeGain =
      safeLiterals._1.foldLeft(0..toFloat) { (acc,k) => max(acc, information.leftMap.getOrElse(k,0..toFloat))  } +
      safeLiterals._2.foldLeft(0..toFloat) { (acc,k) => max(acc, information.rightMap.getOrElse(k,0..toFloat)) }
//    println("Clever " + proof.conclusion + " with " + notDeletedChildren + " children, size " +
//            information.nodeSize + " reg " + regularizeGain)
    (notDeletedChildren - 1).toFloat > regularizeGain
  }
}

trait OptimizedMinLoweringChoice extends RegularizationEvaluation {
// Assumes that only the worst (non-null) regularization of each direct premise will happend.
// Choose to lower in case of equality.
// Shoudl be kept but refactored.
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
    (notDeletedChildren - 1).toFloat >= regularizeGain
  }
}

trait OptimizedMinRegularizationChoice extends RegularizationEvaluation {
// Assumes that only the worst (non-null) regularization of each direct premise will happend.
// Choose to regularize in case of equality.
// Shoudl be kept but refactored.
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
    (notDeletedChildren - 1).toFloat > regularizeGain
  }
}

