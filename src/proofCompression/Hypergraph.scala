///*
// * To change this template, choose Tools | Templates
// * and open the template in the editor.
// */
//
//package proofCompression
//
//import scala.collection.mutable._
//import scala.collection._
//import proofCompression.Utilities._
//import proofCompression.ResolutionCalculus._
//import proofCompression.GUI._
//
//object Hypergraph {
//  val edgeCounter = new Counter
//  val nodeCounter = new Counter
//
//  class Node(p: Proof, c: Clause) {
//    val proof: Proof = p
//    val clause: Clause = c
//    val id: Int = nodeCounter.get
//
//    private var edgesContainingThisNode: List[Edge] = Nil
//    def edges : List[Edge] = edgesContainingThisNode
//    def addEdge(e:Edge) = {
//      edgesContainingThisNode = addEdgeRec(e, edgesContainingThisNode) // edges are sorted first by pivot and then by id.
//    }
//    private def addEdgeRec(e:Edge, edges: List[Edge]): List[Edge] = edges match {
//      case Nil => e::Nil
//      case h::tail => if (e > h) e::edges else h::addEdgeRec(e, tail)
//    }
//    def deleteAllOccurrencesOfEdge(e:Edge) = {edgesContainingThisNode = edgesContainingThisNode.filterNot(edge => edge == e)}
//
//    private def edgesGroupedByPivot : List[List[Edge]] = edgesGroupedByPivotRec(edgesContainingThisNode)
//    private def edgesGroupedByPivotRec(list:List[Edge]): List[List[Edge]]  = list match {
//      case Nil => Nil
//      case e::rest => {
//        val restResult = edgesGroupedByPivotRec(rest)
//        if (restResult.length > 0) {
//          if (restResult.head.head.pivot == e.pivot) return (e::restResult.head)::restResult.tail
//          else return (e::Nil)::restResult
//        } else {
//          return (e::Nil)::Nil
//        }
//      }
//    }
//
//    def this(n1:Node, n2: Node) = {
//      this(Resolvent(n1.proof, n2.proof), resolve(n1.clause, n2.clause))
//      for (e <- n1.edges) {
//        e.deleteNode(n1)
//        e.addNode(this)
//      }
//      for (e <- n2.edges) {
//        e.deleteNode(n2)
//        e.addNode(this)
//      }
//      edgesContainingThisNode = n1.edges ::: n2.edges // merges in a sorted way
//    }
//    def this(nodesToBeMerged:List[Node]) = {
//      this(argmin[Proof](nodesToBeMerged.map(n => n.proof).toList, (p => p.length))._1,nodesToBeMerged.head.clause)
//      for (n <- nodesToBeMerged; e <- n.edges) {
//        e.deleteNode(n)
//        e.addNode(this)
//      }
//      val edgesOfEachNode = nodesToBeMerged.map(n => n.edges).toList
//      def append[T](l1: List[T],l2: List[T]) = l1 ::: l2
//      edgesContainingThisNode = (edgesOfEachNode :\ Nil.asInstanceOf[List[Edge]])(append)
//    }
//
//    def isSplittable: Boolean = {
//      //println("checking splittability for " + this.clause)
//      partitionOfEdges.size >= 2
//    }
//
//    private def partitionOfEdges : mutable.HashSet[mutable.HashSet[Edge]] = {
//      val partition = new mutable.HashSet[mutable.HashSet[Edge]]
//      for (e <- edges) {
//        var wasAdded = false
//        for (part <- partition) {
//          if (wasAdded == false &&
//              !(part contains e) &&
//              (part.exists(otherEdge => (e.resolvent isBelow otherEdge.resolvent)) ||
//               part.forall(otherEdge => (otherEdge.resolvent isBelow e.resolvent))
//              )) {
//            part += e
//            wasAdded = true
//          }
//        }
//        if (wasAdded == false) partition += mutable.HashSet(e)
//      }
//      return partition
//    }
//
//    def split : List[Node] = {
//
//      val partition = partitionOfEdges
//
//      val numberOfNodes = partition.size
//      println(id)
//      println(edges.map(e => e.id + " " + e.pivot))
//      println(numberOfNodes)
//      println(partition)
//      val newNodes = for (i <- 1 to numberOfNodes) yield new Node(proof, clause)
//
//      for (e <- edges) {
//        e.deleteNode(this)
//      }
//
//      require(edges.forall(e => !e.nodes.contains(this) ))
//
//      val newNodesArray = newNodes.toArray
//      val partitionOfEdgesArray = partition.toArray
//      for (i <- 0 to numberOfNodes-1) {
//        val n = newNodesArray(i)
//        val part = partitionOfEdgesArray(i)
//        //println(partitionOfEdges)
//        for (e <- part) {
//          //println(e.id + " ; " + e.pivot + " ; " + e.nodes.map(node => node.id))
//          
//          e.addNode(n)
//          n.addEdge(e)
//          //println(e.nodes.map(node => node.id))
//        }
//      }
//      newNodes.toList
//    }
//
//
//
//    override def toString = {
//      var string = "Node " + id  + " (" + clause + "): " + " (" + proof + "): "
//      for (e <- edges) string += e.id + "; "
//      string
//    }
//  }
//
//
//  class Edge(nodeList: List[Node], r: Resolvent) extends Ordered[Edge] {
//    def resolvent = r
//    def pivot = resolvent.pivot._1.atom
//    def id = edgeCounter.get
//    private var nodesInThisEdge = nodeList
//    def nodes : List[Node] = nodesInThisEdge
//    def nodesAsSet = nodesInThisEdge.toSet
//    def addNode(node:Node) = {nodesInThisEdge = node::nodesInThisEdge}
//    def deleteNode(node:Node) = {nodesInThisEdge = deleteNodeRec(node, nodesInThisEdge)}
//    private def deleteNodeRec(node:Node, list: List[Node]) : List[Node] = {
//      //println(node.id + " : " + list.map(n => n.id))
//      list match {
//        case Nil => throw new Exception("Node not found. Therefore it cannot be deleted.")
//        case n::tail => if (n == node) tail else n::deleteNodeRec(node,tail)
//      }
//    }
//
//    def partitionByPolarity: (List[Node], List[Node]) = nodes.partition(n => n.clause.exists(lit => lit.atom == pivot && lit.polarity == true))
//
//
//    def isResolvable: Boolean = {
//      if (nodesAsSet.size != 2) return false
//      else {
//        val n1 = nodesAsSet.head
//        val n2 = nodesAsSet.last
//        n1.edges.forall(e => e.resolvent isBelow this.resolvent) &&
//        n2.edges.forall(e => e.resolvent isBelow this.resolvent)
//      }
//    }
//
//    def isResolvableNotWorkingButShould: Boolean = {
//      if (false) {
//        println("Is Edge " + id + " resolvable?")
//        println(nodes.size == 2)
//        println((nodes.forall(n => (n.edges.forall(e => e == this || e.pivot != pivot)))))
//      }
//
//      def isSafe: Boolean = {
//        val n1 = nodesAsSet.head
//        val n2 = nodesAsSet.last
//        for (e1 <- n1.edges) {
//          for (e2 <- n2.edges) {
//            if (false) { println(); println((e1,e2)); println(e1 != e2); println(e1.pivot == e2.pivot)}
//            if (e1 != e2 && 
//                e1.pivot == e2.pivot &&
//                !(e1.nodesAsSet(n2) && e2.nodesAsSet(n1))) {return false}
//          }
//        }
//        return true
//      }
//      (nodesAsSet.size == 2) && nodesAsSet.forall(n => !(n.isSplittable)) && isSafe
//    }
//
//    def compare(that: Edge):Int = {
//      if (this.pivot == that.pivot) return this.id - that.id
//      else return this.pivot.compare(that.pivot)
//    }
//    override def toString = {
//      var string = "Edge " + id  + " (" + pivot + "): "
//      for (n <- nodes) string += n.id + "; "
//      string
//    }
//  }
//
//  class ResolutionHypergraph {
//    private val nodes: HashSet[Node] = new HashSet[Node]
//    private val edges: HashSet[Edge] = new HashSet[Edge]
//    def getNodes = nodes.toList
//    def getEdges = edges.toList
//
//    def isTrivial = {nodes.size == 1}
//
//    override def toString = {
//      var string = ""
//      for (e <- edges) string += e.toString + "\n"
//      for (n <- nodes) string += n.toString + "\n"
//      if (isTrivial) string += "Proof length: " + nodes.head.proof.length
//      string
//    }
//
//
//    def this(proof: Proof) = {
//      this()
//      val visitedProofs = new HashSet[Proof]
//      val hashMapInputToNode = new HashMap[Input,Node]
//      buildResolutionHypergraphRec(proof, visitedProofs, hashMapInputToNode)
//    }
//    private def buildResolutionHypergraphRec(proof: Proof,
//                                     visitedProofs: HashSet[Proof],
//                                     hashMapInputToNode: HashMap[Input, Node]) : Unit = {
//      if (!visitedProofs.contains(proof)) {
//        visitedProofs += proof
//        proof match {
//          case Input(c) => {
//              val newNode = new Node(proof, c)
//              hashMapInputToNode += ( proof.asInstanceOf[Input] -> newNode )
//              //println("new input: " + proof.id + " ; " + proof.clause )
//              addNode(newNode)
//          }
//          case Resolvent(left, right) => {
//              buildResolutionHypergraphRec(left,visitedProofs, hashMapInputToNode)
//              buildResolutionHypergraphRec(right,visitedProofs, hashMapInputToNode)
//
//              val (leftPivot,rightPivot) = proof.asInstanceOf[Resolvent].pivot
////              println(left.clause)
////              println(right.clause)
////              println(leftPivot.ancestorInputs.map(c => c.id.toString + " " + c.clause))
////              println(rightPivot.ancestorInputs.map(c => c.id))
////              println(hashMapInputToNode)
////              println()
//
//      //        val leftNodes = leftPivot.ancestorInputs.map(c => hashMapInputToNode(c))
//      //        val rightNodes = rightPivot.ancestorInputs.map(c => hashMapInputToNode(c))
//
//      //        val newEdge = new Edge(leftNodes:::rightNodes, proof.asInstanceOf[Resolvent])
//      //        addEdge(newEdge)
//      //        for (n <- newEdge.nodes) n.addEdge(newEdge)
//          }
//        }
//      }
//    }
//
//
//    def addNode(n:Node) = {nodes += n}
//    private def deleteNode(n:Node) = {nodes -= n}
//
//    def addEdge(e:Edge) = {edges += e}
//    private def deleteEdge(e:Edge) = {edges -= e}
//
//    def simplify = {
//      var counter = 0
//      var resCounter = 0
//      var splitCounter = 0
//      while (!isTrivial && counter < 300) {
//        counter += 1
//        
//        println("Counter: " + counter + " " + resCounter + " " + splitCounter)
//
//        var thereMightBeResolvableEdges = true
//        while (thereMightBeResolvableEdges) {
//          thereMightBeResolvableEdges = false
//          for (e <- edges if e.isResolvable) {
//            resCounter += 1
//            resolveEdge(e)
//            thereMightBeResolvableEdges = true
//          }
//        }
//
//        nodes.find(n => n.isSplittable) match {
//          case Some(splittableNode) => {splitCounter += 1; splitNode(splittableNode)}
//          case None =>
//        }
//
//        //if (edges.forall(e => !e.isResolvable) && nodes.forall(n => !n.isSplittable)) mergeAllSplittedNodes
//
//        if (counter == 299 ) {
//          //invariant
//
//          //val gui = new HypergraphVisualizer
//          //gui.displayHypergraph(this)
//          println(this)
//
//          println("resolvable")
//          for (e <- edges) {
//            println(e.isResolvable)
//          }
//          println("splittable")
//          for (n <- nodes) {
//            println(n.isSplittable)
//          }
//          
//        }
//      }
//    }
//
//    private def invariant = {
//      // Checks if the hypergraph is connected
//      var connected = true
//      for (n <- nodes) {
//        val visitedNodes = new HashSet[Node]
//        var nodesToBeVisited = n::Nil
//        while (nodesToBeVisited.length > 0) {
//          val currentNode = nodesToBeVisited.head
//          nodesToBeVisited = nodesToBeVisited.tail
//          visitedNodes += currentNode
//          for (e <- currentNode.edges; candidateNode <- e.nodes) {
//            if (candidateNode != n && !nodesToBeVisited.contains(candidateNode) && !visitedNodes.contains(candidateNode)) {
//                nodesToBeVisited = candidateNode::nodesToBeVisited
//            }
//          }
//        }
//        if (visitedNodes.size != nodes.size) { connected = false; throw new Exception("Hypergraph has mutually disconnected components") }
//      }
//
//      var stuck = true
//      if (isTrivial) stuck = false
//      for (n <- nodes if n.isSplittable) stuck = false
//      for (e <- edges if (e.isResolvable)) stuck = false
//      for (e1 <- edges; e2 <- edges if (e2 != e1 && e1.pivot == e2.pivot && e1.nodes == e2.nodes) ) stuck = false
//      if (stuck) throw new Exception("Hypergraph simplification is truly stuck")
//
//
//      if (connected && !stuck) true else false
//    }
//
//    val debugResolveEdge = false
//    private def resolveEdge(e: Edge) = {
//      println("Resolving Edge: " + e)
//      if (debugResolveEdge) {
//        println("RESOLVING EDGE - Begin:")
//        println("Edges: " + edges.map(e => e.id))
//        println("Resolving Edge: " + e)
//      }
//      
//      val node1 = e.nodesAsSet.head
//      val node2 = e.nodesAsSet.last
//      deleteEdge(e)
//      node1.deleteAllOccurrencesOfEdge(e)
//      node2.deleteAllOccurrencesOfEdge(e)
//      val resolvedNode = new Node(node1,node2)
//      deleteNode(node1)
//      deleteNode(node2)
//      addNode(resolvedNode)
//
//      if (debugResolveEdge) {
//        println("RESOLVING EDGE - Result:")
//        println("Edges: " + edges.map(e => e.id))
//        println(this)
//        println(" ")
//      }
//    }
//
//
//    val debugSplitNode = false
//    private def splitNode(node: Node) = {
//      if (debugSplitNode) {
//        println("SPLITTING NODE - Begin:")
//        println("Edges: " + edges.map(e => e.id))
//        println("Splitting Node: " + node.id + " having edges: " + node.edges.map(e => e.id))
//      }
//
//      val nodes = node.split
//      for (n <- nodes) {
//        addNode(n)
//      }
//      deleteNode(node)
//
//      if (debugSplitNode) {
//        println("SPLITTING NODE - Result:")
//        println("Edges: " + edges.map(e => e.id))
//        println(this)
//        println(" ")
//      }
//    }
//
//    private def mergeAllSplittedNodes = {
//      println("hey!")
//      for (e <- edges) {
//        //println("EDGE: " + e)
//        val (positiveNodes, negativeNodes) = e.partitionByPolarity
//        val positiveNodesAsSet = positiveNodes.toSet[Node]
//        val negativeNodesAsSet = negativeNodes.toSet[Node]
//        //println("PositiveNodes: " + positiveNodesAsSet.map(n => n.id))
//        //println("NegativeNodes: " + negativeNodesAsSet.map(n => n.id))
//        def mergeIfSplitted(set: scala.collection.immutable.Set[Node]) = if (set.size > 1 && set.forall(n => n.clause == set.head.clause)) {
//          println("SPLITTED!!! :" + set.map(n => n.id) )
//          val newNode = new Node(set.toList)
//          addNode(newNode)
//          for (n <- set) deleteNode(n)
//        }
//        mergeIfSplitted(positiveNodesAsSet)
//        mergeIfSplitted(negativeNodesAsSet)
//      }
//    }
//  }
//}
