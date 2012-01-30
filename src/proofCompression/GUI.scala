///*
// * To change this template, choose Tools | Templates
// * and open the template in the editor.
// */
//
//package proofCompression
//
//import javax.swing.JFrame
//
//import com.mxgraph.swing.mxGraphComponent
//import com.mxgraph.view.mxGraph
////import proofCompression.Hypergraph._
//
//import scala.collection.mutable._
//
//import Math._
//
//object GUI {
//
//  class HypergraphVisualizer {
//    val graph = new mxGraph();
//    val parent = graph.getDefaultParent();
//    val graphComponent = new mxGraphComponent(graph);
//
//    val frame = new JFrame();
//    frame.getContentPane().add(graphComponent);
//    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
//    frame.setSize(600, 400); frame.setVisible(true);
//    
//
//
//    def displayHypergraph(hg: ResolutionHypergraph) = {
//      cleanDisplayedGraph
//      graph.getModel().beginUpdate();
//      val edgeHashMap = new HashMap[Edge,Pair[Object,Pair[Int,Int]]]
//      val nodeHashMap = new HashMap[Node,Pair[Object,Pair[Int,Int]]]
//      val nodes = hg.getNodes
//      val edges = hg.getEdges
//
//      var index = 0
//      val angleInterval = 2*Pi/nodes.length
//      val radius = 40*nodes.length
//      for (n <- nodes) {
//        val angle = index*angleInterval
//        val x = 10 + radius + (radius*cos(angle)).toInt
//        val y = 10 + radius + (radius*sin(angle)).toInt
//        println(n.id + ": " + (x,y))
//        val label : String = n.id + ": " + n.clause
//        val v = addNodeVertex(label, x, y)
//        nodeHashMap += (n -> (v,(x,y)))
//        index += 1
//      }
//
//      for (e <- edges) {
//        val label: String = e.id + ": " + e.pivot
//        var xSum = 0
//        var ySum = 0
//        for (n <- e.nodes) {
//          val position = nodeHashMap(n)._2
//          xSum += position._1
//          ySum += position._2
//        }
//        val x = xSum/e.nodes.length
//        val y = ySum/e.nodes.length
//        val v = addEdgeVertex(label, x, y)
//
//
//        val (positiveNodes, negativeNodes) = e.partitionByPolarity
//        for (n <- positiveNodes.toSet[Node]) {
//          val multiplicity = positiveNodes.count(node => node.id == n.id)
//          addConnection(multiplicity.toString, v, nodeHashMap(n)._1 )
//        }
//        for (n <- negativeNodes.toSet[Node]) {
//          val multiplicity = negativeNodes.count(node => node.id == n.id)
//          addConnection(multiplicity.toString, nodeHashMap(n)._1, v )
//        }
//      }
//      graph.getModel().endUpdate()  
//    }
//
//    def addNodeVertex(label: String, x: Int, y: Int): Object = {
//      return graph.insertVertex(parent, null, label, x, y, label.length * 8, 30)
//    }
//
//    def addEdgeVertex(label: String, x: Int, y: Int): Object = {
//      return graph.insertVertex(parent, null, label, x, y, label.length * 10, 30, "fillColor=yellow")
//    }
//
//    def addConnection(label: String, nodeVertex: Object, edgeVertex: Object): Object = {
//      return graph.insertEdge(parent, null, label, nodeVertex, edgeVertex)
//    }
//
//    def cleanDisplayedGraph = {
//      graph.selectAll()
//      graph.removeCells()
//    }
//
//
//  }
//}