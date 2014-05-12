package at.logic.skeptik.algorithm.dijkstra

import at.logic.skeptik.algorithm.congruence.EqW
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.judgment._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.immutable.{HashMap => IMap}
import scala.collection.mutable.{HashMap => MMap}

class EqTreeEdge(val nextTree: EquationTree, val label: EqLabel) extends (EquationTree,(EqW,Option[(EquationTree,EquationTree)]))(nextTree,label) {
  val eq = label._1
  val deduceTrees = label._2
}

case class EquationTree(val v: E, val pred: Option[EqTreeEdge]) {
  
//  def toProof(eqReferences: MMap[(E,E),EqW]): Option[Proof[N]] = {
////    val istherestill = eqReferences.values.find(p => {(p.toString == "((f1 c_3 c_3) = (f1 (f3 c6) (f3 c7)))" || p.toString == "((f1 (f3 c6) (f3 c7)) = (f1 c_3 c_3))") })
////    println("is there still?: " + istherestill)
//    buildTransChain(eqReferences) match {
//      case Some((Some(node),deduced,eq)) => {
//        
//  //      println(eqReferences.hashCode)
//  //      println("have " + node)
//  //      println("still have to resolve the following deduced nodes: " + deduced)
//        val x = Some(Proof(deduced.foldLeft(node)({(A,B) => 
//          try R(A,B)
//          catch {
//            case e: Exception => {
//              println("=================== BUG ================")
//              println("trans chain node: " + node)
//              println("eqTree: " + this)
//              println("deduced:")
//              println(deduced.mkString("\n"))
//              println("=================== BUG ================")
//              throw e
//            }
//          }
//        })))
//  //      println("results in: " + x)
//        x
//      }
//      case Some((None,ded,_)) if !ded.isEmpty => {
//        if (ded.size > 1) println("more than one deduced with empty node")
//        Some(ded.last)
//      }
//      case _ => None
//    }
//  }
  
    
  def buildTransChain(eqReferences: MMap[(E,E),EqW]): (E,E,Seq[EqW],Seq[(N,EqW)]) = pred match {
    case Some(pr) => {
      val (first,last,equations,deduced) = pr._1.buildTransChain(eqReferences)
      val resFirst = v
      val resEquations = pr._2._1 +: equations
      val resDeduced = pr._2._2 match {
        case None => deduced
        case Some((dd1,dd2)) => {
          (buildDeduction(dd1,dd2,pr._2._1,eqReferences),pr._2._1) +: deduced
        }
      }
      (resFirst,last,resEquations,resDeduced)
    }
    case None => {
      (v,v,Seq(),Seq())
    }
  }
  
  def buildDeduction(dd1: EquationTree, dd2: EquationTree, eq: EqW, eqReferences: MMap[(E,E),EqW]): N = {
    val (dd1Opt, dd2Opt) = (dd1.toProof(eqReferences),dd2.toProof(eqReferences))
    val ddProofs = List(dd1Opt,dd2Opt).filter(_.isDefined).map(_.get)
    val ddProofRoots = ddProofs.map(_.root) //Check for EqAxiom, because of Axiom "hack"
    val ddEqs = ddProofRoots.map(_.conclusion.suc.last).toSeq
//    println("deducing " + eq)
//    println("trees: " + dd1 + " and " + dd2)
//    println("proofs: " + dd1Opt.isDefined + " and " + dd2Opt.isDefined)
    val congr = (eq.l,eq.r) match {
      case (App(u1,u2),App(v1,v2)) => {
        if ((u1 == v1) && (u2 != v2)) EqCongruent(EqW(u2,v2),eq)
        else if ((u1 != v1) && (u2 == v2)) EqCongruent(EqW(u1,v1),eq)
        else if ((u1 != v1) && (u2 != v2)) EqCongruent(EqW(u1,v1),EqW(u2,v2),eq)
        else throw new Exception("Trying to prove the congruence of terms with equal arguments")
      }
      case _ => throw new Exception("Error when creating congruence node, because equality between wrong kind of expressions")
    }
    val res = 
      if (ddEqs.isEmpty) {
        congr
      } 
      else {
        ddProofRoots.foldLeft(congr.asInstanceOf[N])({(A,B) => 
          try EqW.resolveSymm(A,B)
          catch {
            case e: Exception => {
              val AnewAnt = A.conclusion.ant.map(f => if (EqW.isEq(f)) EqW(f).reverse.equality else f)
              val AnewSuc = A.conclusion.suc.map(f => if (EqW.isEq(f)) EqW(f).reverse.equality else f)
              val Anew = 
              println()
              println(this)
              println(A + " " + A.getClass)
              println(B + " " + B.getClass)
              println(Proof(A))
              println(Proof(B))
              throw e
            }
          }
        })
      }
//    println("result:\n"+ Proof(res))
    res
  }
  
//  def transChainProof(eqReferences: MMap[(E,E),App]): Option[Proof[N]] = buildTransChain(eqReferences) match {
//    case Some((Some(node),_,_)) => Some(Proof(node))
//    case Some((_,ded,_)) => Some(ded.last)
//    case _ => None
//  }
  
  def toProof(eqReferences: MMap[(E,E),EqW]): Option[Proof[N]] = {
    val (first,last,equations,deduced) = this.buildTransChain(eqReferences)
    if (equations.size > 1) {
      val transNode = EqTransitive(equations,first,last,eqReferences)
      val res = deduced.foldLeft(transNode.asInstanceOf[N])({(A,B) => 
        val resEq = B._2
        val resNode = B._1
        try {
          R(A,resNode)
        }
        catch {
          case e:Exception => {
            try R(resNode,A)
            catch {
              case e1:Exception => {
                println(this)
                println(A + " " + resNode.getClass())
                println(Proof(resNode)+ " " + resNode.getClass())
//                val oneSide = (resNode.conclusion.suc.contains(resEq) && resNode.conclusion.ant.contains(resEq))
//                val otherSide = (resNode.conclusion.ant.contains(resEq) && resNode.conclusion.suc.contains(resEq))
//                println(oneSide || otherSide)
//              println(this)
//              println("trying to resolve upon " + B._2 + B._2.hashCode)
//              println(Proof(A))
//              println(Proof(B._1))
                throw e1
              }
            }
          }
        }
      })
      Some(res)
    }
    else if (deduced.size == 1) {
      Some(deduced.last._1)
    }
    else None
  }
  
  def eq: Option[EqW] = pred match {
    case Some(pr) => {
      Some(pr._2._1)
    }
    case None => None
  }
  
  def allEqs: Set[EqW] = pred match {
    case Some(pr) => {
//      println(pr._1.v + " deduced eqs: " +deducedEqs)
      pr._1.allEqs + pr._2._1 ++ deducedEqs
    }
    case None => {
      Set()
    }
  }
  
  def originalEqs: Set[EqW] = pred match {
    case Some(pr) => {
      val predOrig = pr._1.originalEqs
      val extra = pr._2._2 match {
        case Some((dd1,dd2)) => dd1.originalEqs union dd2.originalEqs
        case None => Set(pr._2._1)
      }
      predOrig union extra
    }
    case None => Set()
  }
  
  def pathEqs: Set[EqW] = pred match {
    case Some(pr) => {
      pr._1.pathEqs + pr._2._1
    }
    case None => {
      Set()
    }
  }
  
  def deducedEqs: Set[EqW] = {
    val lEqs = leftExpl match {
      case Some(l) => l.originalEqs
      case None => Set()
    }
    val rEqs = rightExpl match {
      case Some(r) => r.originalEqs
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
  
  def firstVert = v
  
  def lastVert: E = pred match {
    case Some(pr) => pr._1.lastVert
    case None => v
  }
  
  def isEmpty = !pred.isDefined
  
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
        case Some(e) => "{"+deducedEqs+"}"//"-["+e+"]" + "{"+deducedEqs+"}"
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