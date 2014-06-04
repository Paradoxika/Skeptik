package at.logic.skeptik.congruence

import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}


abstract class CongruenceNew(
    val rep: Map[E,E], 
    val cclass: Map[E,Set[E]], 
    val lookup: Map[(E,E),E], 
    val lN: Map[E,Set[E]],
    val rN: Map[E,Set[E]],
    val g: CongruenceGraph)
    (implicit eqReferences: MMap[(E,E),EqW]) extends AbstractCongruence {

  def initNode(v: E): CongruenceNew = {
    val newRep = rep + (v -> v)
    val newCclass = cclass + (v -> Set(v))
    val lNNew = lN + (v -> Set[E]())
    val rNNew = rN + (v -> Set[E]())
    newCon(newRep,newCclass,lookup,lNNew,rNNew,g)
  }
  
  def addNode(v: E): CongruenceNew = rep.get(v) match {
    case None => {
      val c0 = this.initNode(v)
      v match {
        case App(a,b) => {
          val c1 = c0.addNode(a).addNode(b)
          val c2 = c1.lookup.get((c1.rep(a),c1.rep(b))) match {
            case Some(term) if (term != v) => {
              c1.merge(term,v,None)
            }
            case _ => c1.updateLookup(c1.lookup.updated((c1.rep(a),c1.rep(b)), v))
          }
          val rNa = c2.rN(c2.rep(a)) + c2.rep(b)
          val lNb = c2.lN(c2.rep(b)) + c2.rep(a)
          val rNnew = c2.rN.updated(c2.rep(a), rNa)
          val lNnew = c2.lN.updated(c2.rep(b),lNb)
          c2.updateLN(lNnew).updateRN(rNnew)
        }
        case _ => c0
      }
    }
    case Some(_) => this
  }
  
  def addAll(eqs: Traversable[EqW]): CongruenceNew = {
    eqs.foldLeft(this)({(A,B) => A.addEquality(B)})
  }
  
  def addEquality(s: E, t: E): CongruenceNew = {
    addEquality(EqW(s,t))
  }
  
  def addEquality(eq: EqW): CongruenceNew = {
    addNode(eq.l).addNode(eq.r).merge(eq.l, eq.r, Some(eq))
  }
  
  def merge(s: E, t: E, eq: Option[EqW]): CongruenceNew = {
    if (rep(s) != rep(t)) {
      val deduced = MSet[(E,E)]((s,t))
      var c = this
      var realEq = eq
      while (!deduced.isEmpty) {
        val (u,v) = deduced.head
        c = c.updateGraph(g.addEdge(u, v, realEq))
        realEq = None
        deduced -= ((u,v))
        if (c.rep(u) != c.rep(v)) {
          c = c.union(u, v, deduced)
        }
      }
      c
    }
    else this
  }
  
  def union(s: E, t: E, deduced: MSet[(E,E)]): CongruenceNew = {
    val (u,v) = if (cclass(rep(s)).size > cclass(rep(t)).size) (s,t) else (t,s)
    val (ru,rv) = (rep(u),rep(v))
//    println("union of " + (s,t) + " rN: " + rN(rv) + " reps: " + rN(rv).map(rep(_)))
    val cR = rN(rv).foldLeft(this)({(A,B) => 
      val rx = A.rep(B)
      val lv = try A.lookup(rv,rx)
      catch {
        case e: Exception => {
          println("trying to access lookup at " + (rv,rx))
          println("lookup: " + A.lookup.mkString(";"))
          println(rv + " right: " + rN(rv).mkString(";"))
          println("rep: " + rep.mkString(";"))
          throw e
        }
      }
//      println("checking " + A.lookup.mkString(",") + " for " + (ru,rx) + " in union of " + (s,t))
      val xDealt = A.lookup.get(ru,rx) match {
        case None => {
//          println("searching for lookup of " + (ru,rx) + " and found none, inserting " + lv + " into " + A.lookup.mkString(","))
          A.updateLookup(A.lookup + ((ru,rx) -> lv))
        }
        case Some(lu) => {
//          println("searching for lookup of " + (ru,rx) + " and found " + lu)
          if (lu != lv) deduced += ((lu,lv))
          A
        }
      }
      xDealt.updateLookup(xDealt.lookup - ((rv,rx)))
    })
    val cL = cR.lN(rv).foldLeft(cR)({(A,B) => 
      val rx = A.rep(B)
      val lv = A.lookup(rx,rv)
      val xDealt = A.lookup.get(rx,ru) match {
        case None => {
//          println("searching for lookup of " + (rx,ru) + " and found none, inserting " + lv + " into " + A.lookup.mkString(","))
          A.updateLookup(A.lookup + ((rx,ru) -> lv))
        }
        case Some(lu) => {
//          println("searching for lookup of " + (rx,ru) + " and found " + lu)
          if (lu != lv) deduced += ((lu,lv))
          A
        }
      }
      xDealt.updateLookup(xDealt.lookup - ((rx,rv)))
    })
//    println("lookup after " + cL.lookup.mkString(","))
    val vClass = cL.cclass(cL.rep(v))
    val newRep = vClass.foldLeft(cL.rep)({(A,B) => 
      A.updated(B, cL.rep(u))
    })
    val uClass = cL.cclass(cL.rep(u)) ++ vClass
    val newCclass = (cL.cclass.updated(cL.rep(u), uClass) - cL.rep(v))
    val vRight = cL.rN(cL.rep(v))
    val vLeft = cL.lN(cL.rep(v))
    val uRight = cL.rN(cL.rep(u)) ++ vRight
    val uLeft = cL.lN(cL.rep(u)) ++ vLeft
    val newRight = (cL.rN.updated(cL.rep(u), uRight) - cL.rep(v))
    val newLeft = (cL.lN.updated(cL.rep(u), uLeft) - cL.rep(v))
    newCon(newRep,newCclass,cL.lookup,newLeft,newRight,cL.g)
  }
  
  def isCongruent(u: E, v: E) = {
    rep(u) == rep(v)
  }
  
  def explain(s: E, t: E): Option[EquationPath]
  
  def subterms(term: E): Seq[E] = term match {
    case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
    case _ => Seq()
  }
  
  def uncurriedTerms(term: E): Seq[E] = term.t match {
    case Arrow(_,_) => {
      term match {
        case App(u,v) => uncurriedTerms(u) ++ uncurriedTerms(v)
        case _ => Seq()
      }
    }
    case _ => Seq(term)
  }
  
  def buildDD(t1: E, eq: Option[EqW], t2: E)(implicit eqReferences: MMap[(E,E),EqW]) = eq match {
    case None => {
      val (sub1,sub2) = (subterms(t1),subterms(t2))
      require(sub1.size == sub2.size)
      val explOpts = (sub1 zip sub2).map(tuple => explain(tuple._1,tuple._2))
      explOpts.filter(_.isDefined).map(_.get).toSet
    }
    case Some(_) => {
//        println("skipping deduce trees!")
      Set[EquationPath]()
    }
  }
  
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): CongruenceNew
  
  def updateRep(newRep: Map[E,E]): CongruenceNew = {
    newCon(newRep,cclass,lookup,lN,rN,g)
  }
  
  def updateCclass(newCclass: Map[E,Set[E]]): CongruenceNew = {
    newCon(rep,newCclass,lookup,lN,rN,g)
  }
  
  def updateLookup(newLookup: Map[(E,E),E]): CongruenceNew = {
    newCon(rep,cclass,newLookup,lN,rN,g)
  }
  
  def updateLN(newLN: Map[E,Set[E]]): CongruenceNew = {
    newCon(rep,cclass,lookup,newLN,rN,g)
  }
  
  def updateRN(newRN: Map[E,Set[E]]): CongruenceNew = {
    newCon(rep,cclass,lookup,lN,newRN,g)
  }
  
  def updateGraph(newG: CongruenceGraph): CongruenceNew = {
    newCon(rep,cclass,lookup,lN,rN,newG)
  }
}