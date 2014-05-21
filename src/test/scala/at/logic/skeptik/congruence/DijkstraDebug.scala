package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.dijkstra._

object DijkstraDebug {

  def main(args: Array[String]):Unit = {
    
    val s = "s"
    val t = "t"
    val x = "x"
    val y = "y"
    val z = "z"
      
    var g = new WGraph[String,Set[String]]()
    
    g = g.addEdge((s,Set("i"),t), 10)
    g = g.addEdge((s,Set("i"),y), 5)
    g = g.addEdge((z,Set("o"),s), 7)
    g = g.addEdge((y,Set("o"),t), 3)
    g = g.addEdge((t,Set("i"),y), 2)
    g = g.addEdge((t,Set("o"),x), 1)
    g = g.addEdge((y,Set("o"),z), 2)
    g = g.addEdge((y,Set("o"),x), 9)
    g = g.addEdge((x,Set("i"),z), 4)
    g = g.addEdge((z,Set("i"),x), 6)
    
    println(g)
    
    val dij = new EquationDijkstra
    
//    dij.apply(s, g)
//    
//    println("shortest path from s to t: " + dij.pi(t))
//    
//    println(dij.distances.mkString(","))
  }
  
}