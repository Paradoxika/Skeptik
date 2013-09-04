package at.logic.skeptik.algorithm.compressor
package split

import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap,HashSet => MSet}
import scala.collection.immutable.{HashSet => Set}

class RecSplit(splitDepth: Int) extends AdditivityHeuristic with DeterministicChoice  {
  
  def apply(proof: Proof[SequentProofNode]) = {
    proof
  }
  
  def positivelyContained(node: SequentProofNode, pivot: E):Boolean = node.conclusion.ant contains pivot
  def negativelyContained(node: SequentProofNode, pivot: E):Boolean = node.conclusion.suc contains pivot
  
  def singleMeasure(node: SequentProofNode):Long = (((node.conclusion.size - (node.premises(0).conclusion.size max node.premises(1).conclusion.size)) max 0) + 1)

  //computes measures of variables while keeping track in what kind of branch (positive or negative) the current node is w.r.t. the pivots seen below
  //positive and negative branches are exclusive. If a node is in both or none of the branches, neither the set for positive nor negative pivots should include that pivot
  //the reason for this is that some pivot can be disabled:
  //a pivot is disabled in branches that originate nodes that contain the pos/neg version of the pivot and which are in a neg/pos branch of this pivot
  //if a node is disabled w.r.t. one pivot, it will never occur in the output of split w.r.t. that pivot and therefore any measures are not counted.
  def computeMeasuresSplitVersion(proof: Proof[SequentProofNode]) = {
    val measures = MMap[E,Set[(Long,Seq[E],Seq[E])]]()
    //children return information:
    //positive pivots: MSet[E]
    //negative pivots: MSet[E]
    //disabled pivots: MSet[E]
    //pivot element: Option[E]
    def visit(node: SequentProofNode, children: Seq[(MSet[E],MSet[E],MSet[E],Option[E])]):(MSet[E],MSet[E],MSet[E],Option[E]) = {
      //combine results from children nodes
      val (pos,neg,disabled) = ((MSet[E](),MSet[E](),MSet[E]()) /: children) ((A,B) => (A._1 union B._1 ,A._2 union B._2,A._3 union B._3))
      //iterate over pivot elements of children and check if this node is start of a positive or negative branch
      children.foreach(C => {
        C._4 match {
          case None =>
          case Some(v) => {
            //current node is start of a positive branch w.r.t. v
            if (positivelyContained(node,v)) {
              //the node is part of a negative branch w.r.t. v -> this pivot counts as disabled in this branch
              if (neg contains v) disabled += v
              //otherwise it is now positive
              else pos += v
            }
            //symmetrical cases to positive cases
            if (negativelyContained(node,v)) { // if / else if --> both cases true means a tautological clause ... should I even take that case into account?
              if (pos contains v) disabled += v
              else neg += v
            }
          }
        }
      })
//      println("node : " + node + " disabled: " + disabled)
      val pivotOption = node match {
        case R(_,_,pivot,_) => {
          if (!(disabled contains pivot)) {
            //if the pivot is not disabled, the actual measure is computed and added to the map of all measures in form of a tuple (measure, positive pivots, negative pivots)
            measures.update(pivot, measures.getOrElse(pivot,Set()) + ((singleMeasure(node),pos.toSeq,neg.toSeq)))
          }
          Some(pivot)
        }
        case _ => None:Option[E]
      }
      //disabled pivots should not count as positive/negative ones, neither should negative ones
      //also ensures that pivots that are both positive and negative are deleted from the sets
      (pos diff (disabled union neg),neg diff (disabled union pos),disabled,pivotOption)
    }
    proof bottomUp visit
    measures
  }
  
  //computes the variable tree using the compute measure method defined above
  def computeVariableTree(proof: Proof[SequentProofNode]) = {
    val measures = computeMeasuresSplitVersion(proof)
    def computeSums(pos: List[E], neg:List[E]):MMap[E,Long] = {
      measures.collect { 
        case (pivot,set) if (!(pos contains pivot) && !(neg contains pivot)) => {
          var sum = 0.toLong
          set.foreach(p => if ((p._2 intersect neg).isEmpty && (p._3 intersect pos).isEmpty) sum = sum + p._1)
          (pivot,sum)
        }
      }
    }
    
    def nextVariable(pos: List[E], neg: List[E], remaining: Int):VariableTree = {
      val p = computeSums(pos,neg).maxBy(_._2)._1
      if (remaining > 1) new VariableTree(p,Some(nextVariable(p::pos,neg,remaining-1)),Some(nextVariable(pos,p::neg,remaining-1)))
      else new VariableTree(p,None,None)
    }
    nextVariable(List(),List(),splitDepth)
  }
  
  //for timing comparison - this is how multisplit computes its variables
  def computeVariablesSeq(proof: Proof[SequentProofNode]) {
    val (measures, measureSum) = computeMeasures(proof)
    var sum = measureSum
    val variableList = {
      def selectVariables(variableList: List[E], remaining: Int):List[E] = if (remaining < 1 || sum < 1) variableList else {
        val selected = chooseVariable(measures, sum)
        sum -= measures(selected)
        measures.remove(selected)
        selectVariables(selected::variableList, remaining - 1)
      }
      selectVariables(List(), splitDepth)
    }
  }
  
  //computes the variable tree by spliting the proof and finding the best variables recursively
  def computeVarTreeWithSplitting(proof: Proof[SequentProofNode]):VariableTree = {
    def nextVariable(proof: Proof[SequentProofNode], remaining: Int):Option[VariableTree] = {
      val (measures, measureSum) = computeMeasures(proof)
      if (measures.isEmpty) None:Option[VariableTree]
      else {
        val p = chooseVariable(measures,measureSum)
        if (remaining == 1) Some(new VariableTree(p,None,None))
        else {
          val spr = new SimpleSplit(p)(proof).root
          val lpp = Proof(spr.premises.head)
          val rpp = Proof(spr.premises.last)
          Some(new VariableTree(p,nextVariable(rpp,remaining-1),nextVariable(lpp,remaining-1)))
        }
      }
    }
    nextVariable(proof,splitDepth).get
  }
}

//class PivotStatus(pos: Set[E],neg: Set[E], disabled: Set[E]) {
//    def union(that: PivotStatus):PivotStatus = new PivotStatus(this.pos union that.pos,this.neg union that.neg, this.disabled union that.disabled)
//}
class VariableTree(variable: E, left: Option[VariableTree], right: Option[VariableTree]) {
  override def toString:String = {
    (left.isDefined,right.isDefined) match {
      case (false,false) => variable.toString()
      case (true,true) => variable + "<" + left.get + ", " + right.get + ">"
      case (true,false) => variable + "<" + left.get + ">"
      case (false,true) => variable + "<" + right.get + ">"
    }
    
  }
}