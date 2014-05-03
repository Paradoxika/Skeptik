package at.logic.skeptik.algorithm.dijkstra

import at.logic.skeptik.expression._
import at.logic.skeptik.proof._
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.judgment._
import at.logic.skeptik.proof.sequent.lk._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import scala.collection.immutable.{HashMap => IMap}

class EqTreeEdgeC(val nextTree: EquationTree, val label: EqLabel) extends (EquationTree,(App,Option[(EquationTree,EquationTree)]))(nextTree,label) {
  val eq = label._1
  val deduceTrees = label._2
}

case class EquationTree(val v: E, val pred: Option[EqTreeEdgeC]) {
  
  def toProof(eqReferences: IMap[(E,E),App]): Option[Proof[N]] = buildTransChain(eqReferences) match {
    case Some((Some(node),deduced,eq)) => {
//      println("have " + node)
//      println("still have to resolve the following deduced nodes: " + deduced)
      val x = Some(Proof(deduced.foldLeft(node)({(A,B) => R(A,B)})))
//      println("results in: " + x)
      x
    }
    case Some((None,ded,_)) if !ded.isEmpty => Some(ded.last)
    case _ => None
  }
  
  def buildDeduction(dd1: EquationTree, dd2: EquationTree, eq: E, eqReferences: IMap[(E,E),App]): N = {
    val (dd1Opt, dd2Opt) = (dd1.toProof(eqReferences),dd2.toProof(eqReferences))
    val ddProofs = List(dd1Opt,dd2Opt).filter(_.isDefined).map(_.get)
    val ddProofRoots = ddProofs.map(_.root) //Check for EqAxiom, because of Axiom "hack"
    val ddEqs = ddProofRoots.map(_.conclusion.suc.last).toSeq
//    println("deducing " + eq)
//    println("trees: " + dd1 + " and " + dd2)
//    println("proofs: " + dd1Opt.isDefined + " and " + dd2Opt.isDefined)
    val res = 
      if (ddEqs.isEmpty) {
        val x = dd1.originalEqs.map(_.asInstanceOf[E]).toSeq ++: dd2.originalEqs.map(_.asInstanceOf[E]).toSeq
        EqCongruent(x,eq)
      } 
      else {
        val congr = EqCongruent(ddEqs)
        try {
          ddProofRoots.foldLeft(congr.asInstanceOf[N])({(A,B) => R(A,B)})
        }
        catch {
          case e:Exception => {
            println("error when building proof for " + eq)
            throw(e)
          }
        }
      }
//    println("result:\n"+ Proof(res))
    res
  }
  
  def transChainProof(eqReferences: IMap[(E,E),App]): Option[Proof[N]] = buildTransChain(eqReferences) match {
    case Some((Some(node),_,_)) => Some(Proof(node))
    case Some((_,ded,_)) => Some(ded.last)
    case _ => None
  }
  
  def buildTransChain(eqReferences: IMap[(E,E),App]): Option[(Option[N],Set[N],E)] = pred match {
    case Some(pr) => {
      val (nextTree, eq, deduceTrees) = (pr.nextTree,pr.eq,pr.deduceTrees)
      if (nextTree.v == v) {
        Some((Some(EqReflexive(v, eqReferences)),Set[N](),eq))
      }
      else {
        val resultFromNext = nextTree.buildTransChain(eqReferences)
  
        resultFromNext match {
          case Some((nodeOpt,deducedRes,eqRes)) => {
            val node = nodeOpt match {
              case Some(nodeRes) => {
                val tr = EqTransitive(eq,nodeRes.conclusion.suc.last,eqReferences)
                val res = R(nodeRes,tr)
                res
              }
              case None => EqTransitive(eq,eqRes,eqReferences)
            }
            val ded = deduceTrees match {
              case Some((ddT1,ddT2)) => Set[N](buildDeduction(ddT1,ddT2,eq,eqReferences))
              case None => Set[N]()
            }
            val dedFinal = ded union deducedRes
//            println("passing on: " + deducedRes + " while proving " + eq)
            Some((Some(node),dedFinal,eq))
          }
          case None => {
            val ded = deduceTrees match {
              case Some((ddT1,ddT2)) => {
                val x = Set[N](buildDeduction(ddT1,ddT2,eq,eqReferences))
//                println("getting the following deduced nodes here: " + x.last + " " + x.last.getClass())
                x
              }
              case None => Set[N]()
            }
//            println("I am here for " + this)
            Some((None,ded,eq))
          }
        }
      }
    }
    case None => None
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
  
  def originalEqs: Set[App] = pred match {
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