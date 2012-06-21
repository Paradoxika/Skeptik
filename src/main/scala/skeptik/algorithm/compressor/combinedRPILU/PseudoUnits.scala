package skeptik.algorithm.compressor

import skeptik.proof.ProofNodeCollection
import skeptik.proof.sequent._
import skeptik.proof.sequent.lk._
import skeptik.judgment._
import skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, LinkedList => LList}
import scala.collection.Map

abstract class AbstractRPILUAlgorithm
extends Function1[SequentProof,SequentProof] {
  protected sealed abstract  class DeletedSide
  protected object LeftDS  extends DeletedSide
  protected object RightDS extends DeletedSide

  def childIsMarkedToDeleteParent(child: SequentProof, parent: SequentProof, edgesToDelete: Map[SequentProof,DeletedSide]) =
    (edgesToDelete contains child) &&
    (edgesToDelete(child) match {
      case LeftDS  => parent == child.premises(0)
      case RightDS => parent == child.premises(1)
    })
  def sideOf(parent: SequentProof, child: SequentProof) = child match {
    // TODO: use premises like above
    case CutIC(left, right, _,_) if parent == left  => LeftDS
    case CutIC(left, right, _,_) if parent == right => RightDS
    case _ => throw new Exception("Unable to find parent in child")
  }

  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, Set[E], Set[E])) => (Set[E],Set[E])
                          ) : (Set[E],Set[E])

  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof

  // A faster size
  def fakeSize[A](l: List[A]) = l match {
    case Nil => 0
    case _::Nil => 1
    case _::_ => 2
  }

  def isUnit(proof: SequentProof, iterator: ProofNodeCollection[SequentProof]) =
    (fakeSize(proof.conclusion.ant) + fakeSize(proof.conclusion.suc) == 1) &&
    (fakeSize(iterator.childrenOf.getOrElse(proof,Nil)) > 1)

  def deleteFromChildren(oldProof: SequentProof, iterator: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) =
    iterator.childrenOf(oldProof).foreach { child =>
      // Deleting both premises of a node being too complicated, regularization takes precedence over unit lowering.
      if (!(edgesToDelete contains child)) edgesToDelete.update(child, sideOf(oldProof, child))
    }

  def fixProofs(edgesToDelete: Map[SequentProof,DeletedSide])
               (p: SequentProof, fixedPremises: List[SequentProof]) = {
    lazy val fixedLeft  = fixedPremises.head;
    lazy val fixedRight = fixedPremises.last;
    p match {
      case Axiom(conclusion) => Axiom(conclusion)
      case CutIC(left,right,_,_) if edgesToDelete contains p => edgesToDelete(p) match {
        case LeftDS  => fixedRight
        case RightDS => fixedLeft
      }
      case CutIC(left,right,auxL,auxR) => ((fixedLeft.conclusion.suc  contains auxL),
                                           (fixedRight.conclusion.ant contains auxR)) match {
        case (true,true) => CutIC(fixedLeft, fixedRight, auxL, auxR)
        case (true,false) => fixedRight
        case (false,true) => fixedLeft
        case (false,false) => heuristicChoose(fixedLeft, fixedRight)
      }
    }
  }
}

trait UnitsCollectingBeforeFixing
extends AbstractRPILUAlgorithm {
  def mapFixedProofs(proofsToMap: Set[SequentProof],
                     edgesToDelete: Map[SequentProof,DeletedSide],
                     iterator: ProofNodeCollection[SequentProof]) = {
    val fixMap = MMap[SequentProof,SequentProof]()
    def visit (p: SequentProof, fixedPremises: List[SequentProof]) = {
      val result = fixProofs(edgesToDelete)(p, fixedPremises)
      if (proofsToMap contains p) fixMap.update(p, result)
      result
    }
    iterator.foldDown(visit)
    fixMap
  }
}

abstract class WeakCombined
extends AbstractRPILUAlgorithm with UnitsCollectingBeforeFixing {

  def lowerInsteadOfRegularize(proof: SequentProof, notDeletedChildren: Int):Boolean

  private def collect(iterator: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    val units = scala.collection.mutable.Queue[SequentProof]()

    def isUnitAndSomething(something: (SequentProof, Int) => Boolean)
                          (p: SequentProof) =
      (fakeSize(p.conclusion.ant) + fakeSize(p.conclusion.suc) == 1) && {
        val aliveChildren = iterator.childrenOf.getOrElse(p,Nil).foldLeft(0) { (acc,child) =>
          if (childIsMarkedToDeleteParent(child, p, edgesToDelete)) acc else (acc + 1)
        }
        (aliveChildren > 1) && (something(p, aliveChildren))
      }
    val isUnitToLower = isUnitAndSomething(lowerInsteadOfRegularize _) _
    val isTrueUnit = isUnitAndSomething { (_,_) => true } _


    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      val (safeL,safeR) = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
      def regularize(position: DeletedSide) = 
        if (isUnitToLower(p)) lower() else {
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
        case CutIC(_,_,_,auxR) if safeL contains auxR => regularize(LeftDS)
        case CutIC(_,_,auxL,_) if safeR contains auxL => regularize(RightDS)
        case p => if (isTrueUnit(p)) lower() else (p, safeL, safeR)
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

abstract class InformedCombined
extends AbstractRPILUAlgorithm with UnitsCollectingBeforeFixing with CombinedIntersection with LeftHeuristicC {

  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])         ):Boolean
  
  def evaluateDerivation(proof: SequentProof, iterator: ProofNodeCollection[SequentProof], aux: E,
                         left:  SequentProof, leftInfo: RegularizationInformation,
                         right: SequentProof, rightInfo:RegularizationInformation):RegularizationInformation

  def collectInformationMap(iterator: ProofNodeCollection[SequentProof]):MMap[SequentProof,RegularizationInformation]

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

trait SimpleCollector
extends InformedCombined {
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
extends InformedCombined {
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
extends InformedCombined {
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

trait AlwaysLowerI extends InformedCombined {
  def lowerInsteadOfRegularize(proof: SequentProof,
                               notDeletedChildren: Int,
                               information: RegularizationInformation,
                               safeLiterals: (Set[E],Set[E])         ):Boolean = true
}
trait AlwaysRegularizeI extends InformedCombined {
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
trait AddEval extends InformedCombined {
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
trait MaxEval extends InformedCombined {
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
trait OptimizedEval extends InformedCombined {
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

abstract class MaxChoice (deletionProbability: Double)
extends InformedCombined {
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
extends InformedCombined {
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
extends InformedCombined {
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
extends InformedCombined {
  def max(x: Float, y: Float) = if (x < y) y else x
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
trait OptChoice extends InformedCombined {
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

trait AlwaysLower extends WeakCombined {
  def lowerInsteadOfRegularize(proof: SequentProof, notDeletedChildren: Int):Boolean = true
}
trait AlwaysRegularize extends WeakCombined {
  def lowerInsteadOfRegularize(proof: SequentProof, notDeletedChildren: Int):Boolean = {
//    println("Irregular unit " + proof.conclusion + " with " + notDeletedChildren + " children")
    false
  }
}

abstract class CombinedRPILU
extends AbstractRPILUAlgorithm {

  def collectEdgesToDelete(iterator: ProofNodeCollection[SequentProof]) = {
    val edgesToDelete = MMap[SequentProof,DeletedSide]()
    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }
      val (safeL,safeR) = computeSafeLiterals(p, childrensSafeLiterals, edgesToDelete, safeLiteralsFromChild _)
      p match {
        case CutIC(_,_,auxL,_) if safeR contains auxL => edgesToDelete.update(p, RightDS)
        case CutIC(_,_,_,auxR) if safeL contains auxR => edgesToDelete.update(p, LeftDS)
        case _ => Unit
      }
      (p, safeL, safeR)
    }
    iterator.bottomUp(visit)
    edgesToDelete
  }

  private def fixProofAndLowerUnits(iterator: ProofNodeCollection[SequentProof], edgesToDelete: MMap[SequentProof,DeletedSide]) = {

    // Ordered list of (pseudo-)units
    var units = LList[(Either[E,E],SequentProof)]()
    // The maximum size (nb of literal in conclusion) for a proof to be added to units
    var unitsLimit = 1
    val literalsDeletedByUnits = (MSet[E](),MSet[E]())

    def afterInsert(oldProof: SequentProof, literal: Either[E,E]) = {
      unitsLimit += 1
      literal match {
        case Left(v)  => literalsDeletedByUnits._1.add(v)
        case Right(v) => literalsDeletedByUnits._2.add(v)
      }
      deleteFromChildren(oldProof, iterator, edgesToDelete)
    }

    // This function scans the units list for insertion, introducing quadratic complexity.
    def scanUnit(oldProof: SequentProof, newProof: SequentProof, introducedLiteral: Either[E,E],
                 literals: (Set[E],Set[E]), size: Int) = {

      def insertUnit(literal: Either[E,E], node: LList[(Either[E,E],SequentProof)]) =
        if (literal == introducedLiteral) {
          node.next = new LList((literal,  newProof), node.next)
          afterInsert(oldProof, literal)
//          println("+ " + newProof.conclusion + " (" + literal + ")")
        }

      // invariant : size <= limit
      def scan(oldLit: (Set[E],Set[E]), size: Int, node: LList[(Either[E,E],SequentProof)], limit: Int):Unit = {
        val newLit = node.elem._1 match {
          case Left(l)  => (oldLit._1, oldLit._2 - l)
          case Right(r) => (oldLit._1 - r, oldLit._2)
        }
        (newLit._1.size, newLit._2.size) match {
          case (1,0) => insertUnit(Left(newLit._1.head),  node)
          case (0,1) => insertUnit(Right(newLit._2.head), node)
          case (l,r) => if (l+r < limit) scan(newLit, l+r, node.next, limit - 1)
        }
      }

      scan(literals, size, units, unitsLimit)
    }

    def reconstructProof(oldProof: SequentProof, fixedPremises: List[SequentProof]) = {
      val newProof = fixProofs(edgesToDelete)(oldProof, fixedPremises)
//      if (isUnit(oldProof,iterator)) println("unit " + oldProof.conclusion + " => " + newProof.conclusion)
      def prependUnit(literal: Either[E,E]) = {
        units = new LList((literal, newProof), units)
        afterInsert(oldProof, literal)
//        println("- " + newProof.conclusion)
      }

      val children = iterator.childrenOf.getOrElse(oldProof, Nil)
      if (fakeSize(children) > 1) {
        // For a node to be lowered we check two conditions which are coded reverse

        // Second condition : literals introduced by lowering the proof node get resolved by preceding units (except one)
        def checkLoweredLiteralGetResolved(remainingLiteral: Either[E,E]) = {
          val literalsIntroducedBylowering = (newProof.conclusion.ant.toSet, newProof.conclusion.suc.toSet)
          (literalsIntroducedBylowering._1.size, literalsIntroducedBylowering._2.size) match {
            case (1,0) => prependUnit(Left(literalsIntroducedBylowering._1.head))
            case (0,1) => prependUnit(Right(literalsIntroducedBylowering._2.head))
            case (l,r) => if (l+r <= unitsLimit) scanUnit(oldProof, newProof, remainingLiteral,
                                                          literalsIntroducedBylowering, l+r)
          }
        }

        // First condition : literals introduced by deleting the proof node from its current positions
        // get resolved by current units (except one)
        val literalsIntroducedByDeletion =
          children.foldLeft((Set[E](),Set[E]())) { (setPair, child) =>
            child match {
              case CutIC(left, right, auxL, auxR) if left  == oldProof => (setPair._1 + auxR, setPair._2)
              case CutIC(left, right, auxL, auxR) if right == oldProof => (setPair._1, setPair._2 + auxL)
              case _ => throw new Exception("Unable to find parent as premise of child")
            }
          }
        val literalsRemainingFromDeletion =
          (literalsIntroducedByDeletion._1 diff literalsDeletedByUnits._2,
           literalsIntroducedByDeletion._2 diff literalsDeletedByUnits._1)

        (literalsRemainingFromDeletion._1.size, literalsRemainingFromDeletion._2.size) match {
          case (0,0) => deleteFromChildren(oldProof, iterator, edgesToDelete)
          case (1,0) => checkLoweredLiteralGetResolved(Right(literalsRemainingFromDeletion._1.head))
          case (0,1) => checkLoweredLiteralGetResolved(Left(literalsRemainingFromDeletion._2.head))
          case _ => Unit
        }
      }
      newProof
    }

    val pseudoRoot = iterator.foldDown(reconstructProof _)
//    println("root " + pseudoRoot.conclusion)
//    println("units " + (units.map(_._1 match { case Left(v) => v ; case Right(v) => v })))
    val orderedUnits = units.foldLeft(List[SequentProof]()) { (lst,u) => (u._2)::lst }
    (pseudoRoot, orderedUnits)
  }

  def apply(proof: SequentProof): SequentProof = {
    val iterator = ProofNodeCollection(proof)
    val edgesToDelete = collectEdgesToDelete(iterator) // TODO: mix this line with the next one
    val (pseudoRoot, units) = fixProofAndLowerUnits(iterator, edgesToDelete)
    units.foldLeft(pseudoRoot) { (left,right) =>
      try {CutIC(left,right)} catch {case e:Exception => left}
    }
  }
}

trait CombinedIntersection
extends AbstractRPILUAlgorithm {
  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, Set[E], Set[E])) => (Set[E],Set[E])
                          ) : (Set[E],Set[E]) = {
    childrensSafeLiterals.filter { x => !childIsMarkedToDeleteParent(x._1, proof, edgesToDelete)} match {
      case Nil  => (Set[E](proof.conclusion.ant:_*), Set[E](proof.conclusion.suc:_*))
      case h::t => t.foldLeft(safeLiteralsFromChild(h)) { (acc, v) =>
        val (safeL, safeR) = safeLiteralsFromChild(v)
        (acc._1 intersect safeL, acc._2 intersect safeR)
      }
    }
  }
}

trait LeftHeuristicC
extends AbstractRPILUAlgorithm {
  def heuristicChoose(left: SequentProof, right: SequentProof):SequentProof = left
}

// TODO: Refactor class and traits hierarchie between LU, RPI and Combined.
abstract class AlwaysLowerInitialUnits
extends CombinedRPILU {
  def computeSafeLiterals(proof: SequentProof,
                          childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])],
                          edgesToDelete: Map[SequentProof,DeletedSide],
                          safeLiteralsFromChild: ((SequentProof, Set[E], Set[E])) => (Set[E],Set[E])
                          ) : (Set[E],Set[E]) =
    throw new Exception("This function should never be called")
  
  override def collectEdgesToDelete(iterator: ProofNodeCollection[SequentProof]) = {
    var (unitsLiteralsL, unitsLiteralsR) = (Set[E](),Set[E]())
    val edgesToDelete = MMap[SequentProof,DeletedSide]()

    def visit(p: SequentProof, childrensSafeLiterals: List[(SequentProof, Set[E], Set[E])]) = {
      def safeLiteralsFromChild(v:(SequentProof, Set[E], Set[E])) = v match {
        case (p, safeL, safeR) if edgesToDelete contains p => (safeL, safeR)
        case (CutIC(left,_,_,auxR),  safeL, safeR) if left  == p => (safeL, safeR + auxR)
        case (CutIC(_,right,auxL,_), safeL, safeR) if right == p => (safeL + auxL, safeR)
        case _ => throw new Exception("Unknown or impossible inference rule")
      }

      var (safeL,safeR) = childrensSafeLiterals.filter { x => !childIsMarkedToDeleteParent(x._1, p, edgesToDelete)} match {
        case Nil  => iterator.foldLeft((Set[E](p.conclusion.ant:_*), Set[E](p.conclusion.suc:_*))) { (acc, p) =>
          (fakeSize(p.conclusion.ant), fakeSize(p.conclusion.suc), fakeSize(iterator.childrenOf.getOrElse(p,Nil))) match {
            case (1,0,2) => (acc._1, acc._2 + p.conclusion.ant(0))
            case (0,1,2) => (acc._1 + p.conclusion.suc(0), acc._2)
            case _ => acc
          }
        }
        case h::t => t.foldLeft(safeLiteralsFromChild(h)) { (acc, v) =>
          val (sL, sR) = safeLiteralsFromChild(v)
          (acc._1 intersect sL, acc._2 intersect sR)
        }
      }

      (fakeSize(p.conclusion.ant), fakeSize(p.conclusion.suc), fakeSize(iterator.childrenOf.getOrElse(p,Nil))) match {
        case (1,0,2) => safeR = safeR intersect unitsLiteralsR ; unitsLiteralsR += p.conclusion.ant(0)
        case (0,1,2) => safeL = safeL intersect unitsLiteralsL ; unitsLiteralsL += p.conclusion.suc(0)
        case _ => Unit
      }

      p match {
        case CutIC(_,right,auxL,_) if (safeR contains auxL) && !isUnit(right,iterator) => edgesToDelete.update(p, RightDS)
        case CutIC(left,_,_,auxR)  if (safeL contains auxR) && !isUnit(left,iterator) => edgesToDelete.update(p, LeftDS)
        case _ => Unit
      }
      (p, safeL, safeR)
    }
    iterator.bottomUp(visit)
//    println("Left  " + unitsLiteralsL)
//    println("Right " + unitsLiteralsR)
    edgesToDelete
  }

}
