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
            case _ => c1.updateLookup(c1.lookup.updated((c1.rep(a),c1.rep(b)), v)) //maybe c1.rep(v) instead of v??
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
      val deducedTest = MSet[(E,E)]()
      var c = this
      var realEq = eq
      while (!deduced.isEmpty) {
        val (u,v) = deduced.head
//        if (realEq == None) println("adding " + (u,v) + " with none")
//        println("graph before adding: " + c.g)
        c = c.updateGraph(c.g.addEdge(u, v, realEq))
//        println("graph after adding: " + c.g)
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
    require(rN.forall(l => l._2.forall(r => lookup.isDefinedAt((rep(l._1),rep(r))))))
    require(lN.forall(l => l._2.forall(r => lookup.isDefinedAt((rep(r),rep(l._1))))))
    val lookupNow = lookup
    val (u,v) = if (cclass(rep(s)).size > cclass(rep(t)).size) (s,t) else (t,s)
    val (ru,rv) = (rep(u),rep(v))
    if (ru != rv) {
      val cR = rN(rv).foldLeft(this)({(A,B) => 
        val rx = A.rep(B)
        val lv = try lookup(rv,rx)
        catch {
          case e: Exception => {
            println("lookup changed?: " + !(lookupNow == A.lookup))
            println("trying to access lookup at " + (rv,rx) + " originals: " + (u,B))
            println("rights: " + rN(rv).mkString(";"))
            println("lookup: " + A.lookup)
            println("class: " + cclass(v))
            throw e
          }
        }
        val xDealt = A.lookup.get(ru,rx) match {
          case None => {
            A.updateLookup(A.lookup + ((ru,rx) -> lv))
          }
          case Some(lu) => {
            val y = if (lu != lv) {
              deduced += ((lu,lv))
              A.updateLookup(A.lookup + ((ru,rx) -> lv))
            }
            else A
            y.updateLookup(y.lookup - ((rv,rx)))
          }
        }
        xDealt.updateLookup(xDealt.lookup - ((rv,rx)))
      })
      val cL = cR.lN(rv).foldLeft(cR)({(A,B) => 
        val rx = A.rep(B)
        val lv = lookup(rx,rv)
        val xDealt = A.lookup.get(rx,ru) match {
          case None => {
  //          println("searching for lookup of " + (rx,ru) + " and found none, inserting " + lv + " into " + A.lookup.mkString(","))
            A.updateLookup(A.lookup + ((rx,ru) -> lv))
          }
          case Some(lu) => {
  //          println("searching for lookup of " + (rx,ru) + " and found " + lu)
            val y = if (lu != lv) {
              deduced += ((lu,lv))
              A.updateLookup(A.lookup + ((rx,ru) -> lv))
            }
            else A
            y.updateLookup(y.lookup - ((rx,rv)))
          }
        }
        xDealt.updateLookup(xDealt.lookup - ((rx,rv)))
      })
  //    println("lookup after " + cL.lookup.mkString(","))
      val vClass = cL.cclass(cL.rep(v))
      val newRep = vClass.foldLeft(cL.rep)({(A,B) => 
        A.updated(B, cL.rep(u))
      })
      val uClass = cL.cclass(newRep(u)) ++ vClass
      val newCclass = (cL.cclass- newRep(v)).updated(newRep(u), uClass)
      val vRight = cL.rN(rv)
      val vLeft = cL.lN(rv)
      val uRight = cL.rN(newRep(u)) ++ vRight
      val uLeft = cL.lN(newRep(u)) ++ vLeft
      val newRight = (cL.rN - rv).updated(newRep(u), uRight)
      val newLeft = (cL.lN - rv).updated(newRep(u), uLeft)
//      var finalRight = newRight
//      vLeft.foreach(l => finalRight = finalRight.updated(l, finalRight(l) - rv))
//      var finalLeft = newLeft
//      vRight.foreach(r => finalLeft = finalLeft.updated(r, finalLeft(r) - rv))
      val bla = newCclass(newRep(s))
      require(newCclass(newRep(s)).contains(s))
      require(cL.lookup.forall(l => newRep.contains(l._1._1) && newRep.contains(l._1._2)))
//      finalRight.foreach(l => {
//        l._2.foreach(r => {
//          if (!cL.lookup.isDefinedAt((newRep(l._1),newRep(r)))) {
//            println("replace " + rep(v) + " with " + rep(u) + " ; " + (ru,rv) + " == " + (ru == rv))
//            println("lookup doesnt contain right " + (newRep(l._1),newRep(r)) + " current lookup\nl:" + cL.lookup.mkString(";") + " init lookup\nl:" + lookup.mkString(";"))
//  //          println("keySet: " + cL.lookup.keySet)
//          }
//        })
//      })
//      finalLeft.foreach(l => {
//        l._2.foreach(r => {
//          if (!cL.lookup.isDefinedAt((newRep(r),newRep(l._1)))) {
//            println("replace " + rep(v) + " with " + rep(u) + " ; " + (ru,rv) + " == " + (ru == rv))
//            println("lookup doesnt contain left " + (newRep(r),newRep(l._1)) + " " + (r,l._1).hashCode() + " current lookup\nl:" + cL.lookup.mkString(";") + " init lookup\nl:" + lookup.mkString(";"))
//            
//  //          println(cL.lookup(r,l._1))
//  //          println("keySet: " + cL.lookup.keySet.head + " == " + (r,l._1) + " ~> " + (cL.lookup.keySet.head eq (r,l._1)))
//          }
//        })
//      })
      require(newRight.forall(l => l._2.forall(r => cL.lookup.isDefinedAt((newRep(l._1),newRep(r))))))
      require(newLeft.forall(l => l._2.forall(r => cL.lookup.isDefinedAt((newRep(r),newRep(l._1))))))
      newCon(newRep,newCclass,cL.lookup,newLeft,newRight,cL.g)
    }
    else this
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
  
  override def toString = {
    "rep: " + rep.mkString(";") + 
    "\ncclass: " + cclass.mkString(";")+ 
    "\nlookup: " + lookup.mkString(";") + 
    "\nrN: " + rN.mkString(";") +
    "\nlN: " + lN.mkString(";") +
    "\ng: " + g
    
  }
}