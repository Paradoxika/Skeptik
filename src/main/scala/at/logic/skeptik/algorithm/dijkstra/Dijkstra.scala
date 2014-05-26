package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.{HashMap => MMap}
import scala.collection.mutable.PriorityQueue
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashSet => MSet}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.congruence.structure.EqW
import scala.math.Ordering.Implicits._


class ArrayDijkstra(references: MMap[(E,E),EqW] = MMap[(E,E),EqW]()) extends EquationDijkstra(references) {
  def newPQ: MyPriorityQueue[E,Int] = {
    new ArrayPQ[E,Int]
  }
}

class FibonacciDijkstra(references: MMap[(E,E),EqW] = MMap[(E,E),EqW]()) extends EquationDijkstra(references) {
  def newPQ: MyPriorityQueue[E,Int] = {
    new FibonacciHeap[E,Int](Integer.MIN_VALUE)
  }
}

/**
 * mutable class Dijkstra implements (a slightly modified version of) Dijkstra's shortest path algorithm
 * 
 * See for example Cormen, T., Leiserson, C., Rivest, R., & Stein, C. (2001). Introduction to algorithms. 
 * Retrieved from http://euler.slu.edu/~goldwasser/courses/loyola/comp363/2003_Spring/handouts/course-info.pdf
 * Page 595 for a description of the algorithm
 * 
 * the algorithm operates on graphs represented as objects of the WGraph class
 * takes two type parameters: T1 is the type of vertices in the graph
 *                            T2 is the type of edge-labels in the graph
 * 
 * the shortest path between vertices is computed and stored as EquationTree objects                           
 * theoretically the class should be independent of the special case of equations,
 * which would require paths objects of a generic type
 * this however turned out to be a little bit tricky and was therefore not dropped (for the moment)
 * 
 * Dijkstra's algorithm is extended by discounting certain edges
 * Since this class was designed to compute explanations and deduced equalities have explanations themselves,
 * some equalities in explanations can be used twice.
 * However, since they only occur once in the final explanation, 
 * they should not be counted twice when computing distances.
 * 
 * Therefore, during the process of computing explanations, certain equalities are discounted,
 * i.e. they have 1 less weight when contributing to another step in the shortest distance path
 * 
 * An idea for improvement:
 * The issue of double using equalities could also be solved by dynamically computing adjacent nodes
 * in the graph.
 * The Dijkstra algorithm relies heavily on adjacent nodes.
 * Should one equation be used in a deduction, all the left and right sides could be made adjacent.
 */

abstract class Dijkstra[T1,T2](eqReferences: MMap[(E,E),EqW]) {
  
  /**
   * distances is always relative to the last input query vertex
   * the map stores the current shortest distances between all nodes and the input vertex
   */
  val distances = MMap[T1,Int]()
  
  /**
   * pathTrees is also relative to the last input vertex
   * similar to distances it stores the paths with the shortest distances
   * 
   * would be nicer if it were something like PathTree[T1,T2] as opposed to EquationTree
   */
  val paths = MMap[T1,EquationPath]()
  
  /**
   * set of equalities, which are discounted
   */
  val discount = MSet[EqW]()
  
  val dataTuples = MMap[T1,DataTuple]()
  
  /**
   * @param u vertex 
   * @res distance of u to the last input vertex or Integer.MAX_VALUE (representing infinity) 
   *      if the distance is not yet computed
   */
  def d(u: T1) = {
    distances.getOrElse(u, Integer.MAX_VALUE)
  }
  
  /**
   * returns the best path from u to the last input vertex
   */
  def pi(u: T1): EquationPath 

  /**
   * creates the edge (u,v) in the (possibly shortest) path between the input expression and v
   * labels that edge with l
   */
  def setPi(u: T1, l: T2, v: T1)
  
  def initPaths(g: WGraph[T1,T2])
  
  def emptyPath(v: T1): EquationPath
  
  def newPQ: MyPriorityQueue[T1,Int]
  
  def isDiscounted(l: T2): Boolean = {
    if (l.isInstanceOf[EqLabel]) {
      val lEqL = l.asInstanceOf[EqLabel]
      val eq = lEqL._1
      discount.contains(eq)
    }
    else false
  }
  
      /**
     * @return the actual weight of an edge of the graph, 
     *         which is: - its weight in the graph if the edge is not discounted
     *                   - its weight in the graph - 1 if it is
     */
    def w(u: T1, l: T2, v: T1): Int // = {
//      val w1 = g.weights.getOrElse((u,l,v), Integer.MAX_VALUE) // could be improved!
////      if (isDiscounted(l)) {
////        w1 - 1
////      }
////      else w1
//      w1
//    }
  
  /**
   * @return the shortest path between s and target in the graph g where
   *         - shortest path is s <-{s = s}- s, if s == target 
   *         (this is the only point where this class can create an equality
   *         and possibly this situation should be handeled in another position)
   *         
   *         - shortest to all nodes are calculated with the main apply method
   *         and the path to the target node is returned
   */
  
  def apply(s: T1, target: T1, g: WGraph[T1,T2]): EquationPath = {
    if (s == target && s.isInstanceOf[E]) {
      val sE = s.asInstanceOf[E]
      val end = new EquationPath(sE,None)
      val x = EqW(sE,sE,eqReferences)
      val eqTreeEdge = new EqTreeEdge(end,EqLabel(x,None))
      new EquationPath(sE,Some(eqTreeEdge))
    }
    else {
      this(s,g)
      paths.getOrElse(target,emptyPath(target))
    }
  }
  
  
  /**
   * This method performs the shortest path finding algorithm of Dijkstra
   * it computes paths and distances from some node s to all other nodes in the graph
   * 
   * 
   * @param s source node
   * @param g graph where shortest paths should be searched
   */
  def apply(s: T1, g: WGraph[T1,T2]): Unit = {
//    var g = gIn // had this, but I don't think I need it still
    distances.clear
    paths.clear
    discount.clear
    dataTuples.clear
    
//    println("new search")
    
    initPaths(g)
    
    distances += (s -> 0)
    
    val q = newPQ
//    val q = new ArrayPQ[T1,Int]()
//    val q = new FibonacciHeap[T1,Int](Integer.MIN_VALUE)

    g.vertices.foreach(v => {
//      q.insert(v, d(v))
      val dT = DataTuple(v,d(v))
//      if (v.toString == "(f1 (f3 c_2) c_2)") println(" adding it! ")
      dataTuples += (v -> dT)
      q.insert(v,d(v))
    })
//    println("finished adding")

    
    def relax(u: T1, l: T2, v: T1) = {
      val y = d(u).toLong + w(u,l,v).toLong
      val x = if (y >= Integer.MAX_VALUE) Integer.MAX_VALUE else y.toInt
      if (d(v) > x) {
        val oldDT = dataTuples(v)
        val newDT = DataTuple(v,x)
        dataTuples.update(v, newDT)
        distances.update(v, x)
        setPi(v,l,u)
        q.decreaseKey(v, x)
//        q.decreaseKey(oldDT, newDT)
      }
    }
    
    while(!q.isEmpty) {
      q.extractMin match {
        case None =>
        case Some(u) => {
//          val l = pi(u.key).originalEqs //Only origianl Eqs are in the graph
//          l.foreach(lE => {
//            discount += lE
//          })
          
          /**
           * if adjacend would be dynamic, discounts could be taken into account here
           */
          val adj = g.adjacent(u) //Slow line!
          adj.foreach(x => {
//            println("relaxing " + (u,x._2))
            relax(u,x._1,x._2)
          })
        }
      }
    }
  }  
  
  class distOrder extends Ordering[T1] {
    override def compare(a: T1, b: T1) = - (d(a) compare d(b))
  }
  
  case class DataTuple(val key: T1, val value: Int) extends Ordered[DataTuple] {
    def compare(that: DataTuple) = this.value compare that.value
  }
}


/**
 * EquationDijkstra is of type Dijkstra with types E for vertices and EqLabel for edge labels
 * 
 * implements the path methods pi and setPi using EquationTree objects
 */

abstract class EquationDijkstra(references: MMap[(E,E),EqW] = MMap[(E,E),EqW]()) extends Dijkstra[E,EqLabel](references) {
  
  def w(u: E, l: EqLabel, v: E) = {
    l.size
  }
  
  def emptyPath(v: E): EquationPath = {
    new EquationPath(v,None)
  }
  
  def initPaths(g: WGraph[E,EqLabel]) = {
    g.vertices.foreach(v => {
      paths += (v -> new EquationPath(v,None))
    })
  }
  
  def pi(u: E): EquationPath = {
    paths(u)
  }
  
  def setPi(u: E, l: EqLabel, v: E) = {
    val eqTreeEdge = new EqTreeEdge(pi(v),l)
    val p = new EquationPath(u,Some(eqTreeEdge))
    pUpdate(u,p)
  }
  
  def pUpdate(u: E, p: EquationPath) = {
    paths.update(u,p)
  }
}