package at.logic.skeptik.congruence.structure

import at.logic.skeptik.expression._
import at.logic.skeptik.algorithm.dijkstra._
import scala.collection.mutable.{ListBuffer, StringBuilder, HashMap => MMap}

case class ProofForest(next: Map[E,(E,Option[EqW])] = Map[E,(E,Option[EqW])](), rootSize: Map[E,Int] = Map[E,Int]()) extends CongruenceGraph {
  
  def addEdge(u: E, v: E, eq: Option[EqW]) = {
    val uR = root(u)
    val vR = root(v)
    if (uR != vR) {
      val uIn = if (!rootSize.isDefinedAt(uR)) ProofForest(next,rootSize + (u -> 1)) else this
      val vIn = if (!rootSize.isDefinedAt(v)) ProofForest(uIn.next,uIn.rootSize +(v -> 1)) else uIn
      if (vIn.rootSize(uR) > vIn.rootSize(vR)) {
        vIn.insertEdge(u,uR,v,vR,eq)
      }
      else {
        vIn.insertEdge(v,vR,u,uR,eq)
      }
    }
    else this
  }
  
  def root(u: E) = {
    var node = u
    while (next.isDefinedAt(node)) {
      node = next(node)._1
    }
    node
  }
  
  def reversePathList(orig: List[(E,Option[EqW],E)]) = {
    orig.foldLeft(List[(E,Option[EqW],E)]())({(A,B) => 
      A.+:((B._3,B._2,B._1))
    })
  }
  
  def ncaPath(u: E, v: E) = {
    val p1 = rootPath(u)
    val p2 = rootPath(v)
    if (p1.lastOption.getOrElse((u,None,u))._3 == p2.lastOption.getOrElse((v,None,v))._3) {
      val path = p1.diff(p2) ++ reversePathList(p2.diff(p1))
      if (root(u) != root(v) && !path.isEmpty) println("building path for non congruent terms: " + (u,v))
      path
    }
    else List()
    
  }
  
  /**
   * Let c be the nearest common ancestor of u and v in the proof tree
   * The explanation in form of an EquationPath is found by traversing the path from u to c concatinated with the path from c to v.
   * In each step of the path, if an equation is set as edge label, it is original and no deduce paths have to be created.
   * If no equation is set, then the equality has to be deduced and paths for the two arguments are created
   */
  def explain(u: E, v: E)(implicit eqReferences: MMap[(E,E),EqW]): Option[EquationPath] = {
    val path = ncaPath(u,v) 
    if (path.isEmpty) {
      if (u == v) Some(new EquationPath(u,None))
      else None
    }
    else {
      val x = explainAlongPath(path)
      
      if (!(((x.firstVert == u) && (x.lastVert == v)) || ((x.firstVert == v) && (x.lastVert == u)))){
        println("faulty expl for " + (u,v) + "\n"+path)
      }
      Some(x)
    }
  }
  
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
  
  def explainAlongPath(path: List[(E,Option[EqW],E)])(implicit eqReferences: MMap[(E,E),EqW]): EquationPath = {
//    println(path)
    val (t1,eq,t2) = path.head
    var end = false
    val realEq = eq.getOrElse({
      val x = EqW(t1,t2,false) //Probably causing bugs!
//      if (x.toString == "((f1 c_1) = (f1 (f1 c_2 c_3)))") println("creating ((f1 c_1) = (f1 (f1 c_2 c_3))) in explainAlongPath")
//      if (x.toString == "((f1 c_1) = (f1 (f1 c_2 c_3)))") println("creating ((f1 c_1) = (f1 (f1 c_2 c_3))) in explainAlongPath")
      x
    })
    val deduceTrees = buildDD(t1,eq,t2)
//    println(eq + " real eq: " + realEq)
    val eqL = EqLabel(realEq,deduceTrees)
    val nextEdge = if (path.size > 1)
      explainAlongPath(path.tail)
    else {
//      println(path + " ending!")
      end = true
      val x = new EquationPath(t2,None)
//      println(x)
      x
    }
    val eqEdge = EqTreeEdge(nextEdge,eqL)
    val y = new EquationPath(t1,Some(eqEdge))
//    if (end) println(y)
    y
  }
  
  def rootPath(u: E) = {
    val path = ListBuffer[(E,Option[EqW],E)]()
    var node = u
    while (next.isDefinedAt(node)) {
      val nn = next(node)
      path.+=((node,nn._2,nn._1))
      node = nn._1
    }
    path.toList
  }
  
  private def insertEdge(u: E, uRoot: E, v: E, vRoot: E, eq: Option[EqW]): ProofForest = {
//    println("adding " + v + " to " + u)
    val reversed = reverseToRoot(v)
    val finalSize = reversed.rootSize.updated(uRoot,reversed.rootSize(uRoot) + reversed.rootSize(vRoot)) - v
    val finalNext = reversed.next.updated(v, (u,eq))
    ProofForest(finalNext,finalSize)
  }
  
  def reverseToRoot(u: E): ProofForest = {
//    println("reversing " + u)
    val path = rootPath(u)
    val revNext = path.foldLeft(next)({(A,B) =>
      val (node1,eq,node2) = B
      A.updated(node2,(node1,eq))
    })
    val finalNext = revNext - u
    ProofForest(finalNext,rootSize)
  }
  
  def printNode(u: E) = {
    var node = u
    var out = new StringBuilder
    while (next.isDefinedAt(node)) {
      out.append(node +" -> ")
      node = next(node)._1
    }
    out.append(node.toString)
  }
}