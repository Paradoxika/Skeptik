package at.logic.skeptik.algorithm.dijkstra

import at.logic.skeptik.expression._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.judgment._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

class EqTreeEdgeC(val nextTree: EquationTree, val label: EqLabel) extends (EquationTree,(App,Option[(EquationTree,EquationTree)]))(nextTree,label) {
  val eq = label._1
  val deduceTrees = label._2
}

case class EquationTree(val v: E, val pred: Option[EqTreeEdgeC]) {
  
  def toProof: Option[Proof[N]] = toProof(None,None)
  
  def toProof(lastResult: Option[N], lastEq: Option[E]): Option[Proof[N]] = pred match {
    case Some(pr) => {
      val (nextTree, eq, deduceTrees) = (pr.nextTree,pr.eq,pr.deduceTrees)
      val transNode = lastResult match {
        case Some(res) => {
          val transEq = res.conclusion.suc.last
          Some(EqTransitive(eq,transEq))
        }
        case None => {
          lastEq match {
            case Some(lEq) => {
              Some(EqTransitive(eq,lEq))
            }
            case None => None
          }
        }
      }
      val resultFromChain = nextTree.toProof(transNode, Some(eq))
      val fullTrans = transNode match {
        case Some(trN) => {
          resultFromChain match {
            case Some(proof) => Some(R(proof.root,trN))
            case None => transNode
          }
        }
        case None => resultFromChain match {
            case Some(proof) => Some(proof.root)
            case None => None
          }
        }
      
      val deduceCongruence = deduceTrees match {
        case Some((dd1,dd2)) => {
          val (dd1Opt, dd2Opt) = (dd1.toProof,dd2.toProof)
          val ddProofs = List(dd1Opt,dd2Opt).filter(_.isDefined).map(_.get)
          val ddProofRoots = ddProofs.filter(!_.root.isInstanceOf[Axiom]).map(_.root) //Check for EqAxiom, because of Axiom "hack"
          val ddEqs = ddProofs.map(_.root.conclusion.suc.last).toSeq
          val congr = EqCongruent(ddEqs,eq)
//          println("ddProofRoots: " + ddProofRoots)
//          println("ddProofs: " + ddProofs)
          val res = ddProofRoots.foldLeft(congr.asInstanceOf[N])({(A,B) => R(A,B)})
          Some(res)
        }
        case None => None
      }
//      println("EqTree, deduceCong: " + deduceCongruence)
////      println("from: " + deduceTrees.getOrElse(("a","b"))._1 + " and " + deduceTrees.getOrElse(("a","b")._2))
//      if (deduceTrees.isDefined) {
//        println("1: " + deduceTrees.get._1)
//        println("2: " + deduceTrees.get._2)
//        println("all: " + deduceTrees)
//      }
      val finalResult = fullTrans match {
        case Some(trans) => {
          deduceCongruence match {
            case Some(proof) => {
              val p = Proof(R(trans,proof).asInstanceOf[N]) //why doesnt it work without asInstanceOf[N]??
              Some(p)
            }
            case None => Some(Proof(trans))
          }
        }
        case None => None
      }
      finalResult
    }
    case None => lastResult match {
      case Some(_) => None
      case None => {
        lastEq match {
          case Some(lEq) => {
            Some(Axiom(new Sequent(Seq(),Seq(lEq)))) //This is a little bit of a hack
          }
          case None => {
            if (v.t == i) {
//              println("HERE at " + this)
              Some(EqReflexive(v)) 
            }
            else None
          }
        }
      }
    }
  }
  
  def bla(node: N) = {
    val x = node.conclusion
    val y = x.ant
    y
  }
  def eq: Option[App] = pred match {
    case Some(pr) => {
      Some(pr._2._1)
    }
    case None => None
  }
  
  def allEqs: Set[App] = pred match {
    case Some(pr) => {
//      println(pr._1.v + " deduced eqs: " +deducedEqs)
      pr._1.allEqs + pr._2._1 ++ deducedEqs
    }
    case None => {
      Set()
    }
  }
  
  def pathEqs: Set[App] = pred match {
    case Some(pr) => {
      pr._1.pathEqs + pr._2._1
    }
    case None => {
      Set()
    }
  }
  
  def deducedEqs: Set[App] = {
    val lEqs = leftExpl match {
      case Some(l) => l.pathEqs
      case None => Set()
    }
    val rEqs = rightExpl match {
      case Some(r) => r.pathEqs
      case None => Set()
    }
    lEqs ++ rEqs
  }
  
  def predTree: Option[EquationTree] = pred match {
    case Some(pr) => Some(pr._1)
    case None => None
  }
  
  def leftExpl: Option[EquationTree] = pred match {
    case Some(pr) => pr._2._2 match {
      case Some((l,r)) => Some(l)
      case None => None
    }
    case None => None
  }
  
  def rightExpl: Option[EquationTree] = pred match {
    case Some(pr) => pr._2._2 match {
      case Some((l,r)) => Some(r)
      case None => None
    }
    case None => None
  }
  
  def collectLabels: Set[EqLabel] = pred match {
    case Some(pr) => {
      val z = pr._2
      val y = pr._1.collectLabels
      val x = y + z
//      println("label at " + v + " ~ " + y + " + " + z + " <==> " + x)
      x
    }
    case None => {
      Set()
    }
  }
    
  override def toString: String = toString(true)
  
  def toString(labels: Boolean): String = {
    val pString = pred match {
      case Some(pr) => {
        
      }
      case None => ""
    }
    val predLabel = 
      if (labels) eq match {
        case Some(e) => "-["+e+"]" + "{"+deducedEqs+"}"
        case None => ""
      }
      else ""
    val predString = predTree match {
        case Some(pT) => pT.toString(labels)
        case None => ""
      }
//    println("pT def at "+v+" ?: " + predTree.isDefined + " String: " + predString)
    "<~" + v + predLabel + predString
  }
}

//object PathTree[T1,T2] {
//  def apply(v: T1, pred: T2){
//    
//  }
//}

/*****
 * T1: vertix label
 * T2: edge label
 * T3: successor type
 */

//abstract class PathTree[T1,T2 <: Option[(T3,T4)],T3 <: PathTree[T1,T2,T3,T4],T4](val v: T1, val pred: T2) {
//  
//  override def toString = {
//    if (pred.isDefined) {
//      v + " <" + pred.get._2 + "- " + pred.get._1
////      v + ", " + pred.get._1
//    }
//    else {
//      v.toString
//    }
//  }
//  
//  def toProof: Boolean = {
//    if (pred.isDefined) {
//      val x = (pred.get._1.v == v)
//      if (!x) println(v + " is not equal to " + pred.get._1.v)
//      else println(v + " is equal to " + pred.get._1.v)
//      x && pred.get._1.toProof
//    }
//    else true
//  }
//  
//  def collectVertices: List[T1] = {
//    if (pred.isDefined) {
//      v +: pred.get._1.collectVertices
//    }
//    else {
//      List(v)
//    }
//  }
//  
//  def depth: Int = {
//    if (pred.isDefined) {
//      1 + pred.get._1.depth
//    }
//    else {
//      0
//    }
//  }
////  def sumWeights: Int = {
////    if (pred.isDefined) {
////      pred.get._3 + pred.get._1.sumWeights
////    }
////    else {
////      0
////    }
////  }
//
//  def lastLabel: Option[T4] = {
//    if (pred.isDefined) {
//      Some(pred.get._2)
//    }
//    else None
//  }
//  
//  def collectLabels: Set[T4] = {
//    if (pred.isDefined) {
//      val z = pred.get._2
//      val y = pred.get._1.collectLabels
//      val x = y + z
////      println("label at " + v + " ~ " + y + " + " + z + " <==> " + x)
//      x
//    }
//    else {
//      Set()
//    }
//  }
//}