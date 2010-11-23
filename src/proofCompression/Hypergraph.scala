/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package proofCompression

import scala.collection.mutable._
import proofCompression.Utilities._
import proofCompression.ResolutionCalculus._
import proofCompression.GUI._

object Hypergraph {
  val EdgeCounter = new Counter
  val NodeCounter = new Counter

  class Node(p: ResolutionProof, c: Clause) {
    val proof: ResolutionProof = p
    val clause: Clause = c
    val id: Int = NodeCounter.get

    private var edgesContainingThisNode: List[Edge] = Nil
    def edges : List[Edge] = edgesContainingThisNode
    def addEdge(e:Edge) = {
      edgesContainingThisNode = addEdgeRec(e, edgesContainingThisNode) // edges are sorted first by pivot and then by id.
    }
    private def addEdgeRec(e:Edge, edges: List[Edge]): List[Edge] = edges match {
      case Nil => e::Nil
      case h::tail => if (e > h) e::edges else h::addEdgeRec(e, tail)
    }
    def deleteAllOccurrencesOfEdge(e:Edge) = {edgesContainingThisNode = edgesContainingThisNode.filterNot(edge => edge == e)}

    private def edgesGroupedByPivot : List[List[Edge]] = edgesGroupedByPivotRec(edgesContainingThisNode)
    private def edgesGroupedByPivotRec(list:List[Edge]): List[List[Edge]]  = list match {
      case Nil => Nil
      case e::rest => {
        val restResult = edgesGroupedByPivotRec(rest)
        if (restResult.length > 0) {
          if (restResult.head.head.pivot == e.pivot) return (e::restResult.head)::restResult.tail
          else return (e::Nil)::restResult
        } else {
          return (e::Nil)::Nil
        }
      }
    }

    def this(n1:Node, n2: Node) = {
      this(Resolvent(n1.proof, n2.proof),resolve(n1.clause,n2.clause))
      for (e <- n1.edges) {
        e.deleteNode(n1)
        e.addNode(this)
      }
      for (e <- n2.edges) {
        e.deleteNode(n2)
        e.addNode(this)
      }
      edgesContainingThisNode = merge(n1.edges,n2.edges) // merges in a sorted way
    }
    def this(nodesToBeMerged:List[Node]) = {
      this(argmin(nodesToBeMerged.map(n => n.proof).toList, proofLength)._1,nodesToBeMerged.head.clause)
      for (n <- nodesToBeMerged; e <- n.edges) {
        e.deleteNode(n)
        e.addNode(this)
      }
      val edgesOfEachNode = nodesToBeMerged.map(n => n.edges).toList
      edgesContainingThisNode = merge(edgesOfEachNode)
    }
    private def merge(list1: List[Edge],list2: List[Edge]): List[Edge] = {
      (list1, list2) match {
        case (Nil, _) => list2
        case (_, Nil) => list1
        case (h1::t1, h2::t2) => {
          if (h1 >= h2) h1 :: merge(t1, list2)
          else h2 :: merge(list1, t2)
        }
      }
    }
    private def merge(listOfListsOfEdges: List[List[Edge]]): List[Edge] = {
      val emptyList: List[Edge] = Nil
      (listOfListsOfEdges :\ emptyList)(merge)
    }
 
//    def isSplittable: Boolean = {
//      val edgesGBP : List[List[Edge]] = edgesGroupedByPivot
//      edgesGBP.exists(list => list.toSet[Edge].size > 1) &&
//      (1 < gcd(edgesGBP.map(l => l.length).toList))
//    }

    def isSplittable: Boolean = {
      println("checking splittability for " + this.clause)
      if (edges.length == 0) return false
      for (edge <- edges; if edges.forall(e => e.resolvent isBelow edge.resolvent)) {
        println(edge.id + " dominates. Not splittable.")
        return false
      }
      println("splittable.")
      return true
    }

    def split : List[Node] = {
      val edgesGBP = edgesGroupedByPivot
      val edgesGBPLengths = edgesGBP.map(list => list.length)
      val numberOfNodes = gcd(edgesGBPLengths)
      val newNodes = for (i <- 1 to numberOfNodes) yield new Node(proof, clause)
      val numberOfEdgesPerNode = edgesGBPLengths.map(length => length / numberOfNodes)
      var nodeIndex = 0
      for (n <- newNodes) {
        var edgeGroupIndex = 0
        for (edgeGroup <- edgesGBP) {
          for (edgeIndex <- (nodeIndex*numberOfEdgesPerNode(edgeGroupIndex)) to ((nodeIndex+1)*numberOfEdgesPerNode(edgeGroupIndex) - 1)) {
            val e = edgeGroup(edgeIndex)
            e.deleteNode(this)
            e.addNode(n)
            n.addEdge(e)
          }
          edgeGroupIndex += 1
        }
        nodeIndex += 1
      }
      newNodes.toList
    }



    override def toString = {
      var string = "Node " + id  + " (" + clause + "): " + " (" + proof + "): "
      for (e <- edges) string += e.id + "; "
      string
    }
  }


  class Edge(nodeList: List[Node], r: Resolvent) extends Ordered[Edge] {
    def resolvent = r
    def pivot = resolvent.pivot._1.atom
    def id = resolvent.id
    private var nodesInThisEdge = nodeList
    def nodes : List[Node] = nodesInThisEdge
    def nodesAsSet = nodesInThisEdge.toSet
    def addNode(node:Node) = {nodesInThisEdge = node::nodesInThisEdge}
    def deleteNode(node:Node) = {nodesInThisEdge = deleteNodeRec(node, nodesInThisEdge)}
    private def deleteNodeRec(node:Node, list: List[Node]) : List[Node] = {
      //println(node.id + " : " + list.map(n => n.id))
      list match {
        case Nil => throw new Exception("Node " + node.id + " not found in edge " + id + ". Therefore it cannot be deleted.")
        case n::tail => if (n == node) tail else n::deleteNodeRec(node,tail)
      }
    }

    def partitionByPolarity: (List[Node], List[Node]) = nodes.partition(n => n.clause.exists(lit => lit.atom == pivot && lit.polarity == true))

    def isResolvable: Boolean = {
      if (false) {
        println("Is Edge " + id + " resolvable?")
        println(nodes.size == 2)
        println((nodes.forall(n => (n.edges.forall(e => e == this || e.pivot != pivot)))))
      }

      def isSafe: Boolean = {
        val n1 = nodesAsSet.head
        val n2 = nodesAsSet.last
        for (e1 <- n1.edges) {
          for (e2 <- n2.edges) {
            if (false) { println(); println((e1,e2)); println(e1 != e2); println(e1.pivot == e2.pivot)}
            if (e1 != e2 && e1.pivot == e2.pivot) {return false}
          }
        }
        return true
      }
      (nodesAsSet.size == 2) && (nodesAsSet.forall(n => (n.edges.forall(e => e == this || e.pivot != pivot)))) && isSafe
    }

    def compare(that: Edge):Int = {
      if (this.pivot == that.pivot) return this.id - that.id
      else return this.pivot.compare(that.pivot)
    }
    override def toString = {
      var string = "Edge " + id  + " (" + pivot + "): "
      for (n <- nodes) string += n.id + "; "
      string
    }
  }

  class ResolutionHypergraph {
    private val nodes: HashSet[Node] = new HashSet[Node]
    private val edges: HashSet[Edge] = new HashSet[Edge]
    def getNodes = nodes.toList
    def getEdges = edges.toList

    def isTrivial = {nodes.size == 1}

    override def toString = {
      var string = ""
      for (e <- edges) string += e.toString + "\n"
      for (n <- nodes) string += n.toString + "\n"
      if (isTrivial) string += "Proof length: " + proofLength(nodes.head.proof)
      string
    }


    def this(proof: ResolutionProof) = {
      this()
      val visitedProofs = new HashSet[ResolutionProof]
      val hashMapInputToNode = new HashMap[Input,Node]
      buildResolutionHypergraphRec(proof, visitedProofs, hashMapInputToNode)
    }
    private def buildResolutionHypergraphRec(proof: ResolutionProof,
                                     visitedProofs: HashSet[ResolutionProof],
                                     hashMapInputToNode: HashMap[Input, Node]) : Unit = {
      if (!visitedProofs.contains(proof)) {
        visitedProofs += proof
        proof match {
          case Input(c) => {
              val newNode = new Node(proof, c)
              hashMapInputToNode += ( proof.asInstanceOf[Input] -> newNode )
              addNode(newNode)
          }
          case Resolvent(left, right) => {
              buildResolutionHypergraphRec(left,visitedProofs, hashMapInputToNode)
              buildResolutionHypergraphRec(right,visitedProofs, hashMapInputToNode)

              val (leftPivot,rightPivot) = proof.asInstanceOf[Resolvent].pivot
              val leftNodes = leftPivot.ancestorInputs.map(c => hashMapInputToNode(c))
              val rightNodes = rightPivot.ancestorInputs.map(c => hashMapInputToNode(c))
              val newEdge = new Edge(leftNodes:::rightNodes, proof.asInstanceOf[Resolvent])
              addEdge(newEdge)
              for (n <- newEdge.nodes) n.addEdge(newEdge)
          }
        }
      }
    }


    def addNode(n:Node) = {nodes += n}
    private def deleteNode(n:Node) = {nodes -= n}

    def addEdge(e:Edge) = {edges += e}
    private def deleteEdge(e:Edge) = {edges -= e}

    def simplify = {
      var counter = 0
      var resCounter = 0
      var splitCounter = 0
      while (!isTrivial && counter < 130) {
        counter += 1
        
        println("Counter: " + counter + " " + resCounter + " " + splitCounter)

        var thereMightBeResolvableEdges = true
        while (thereMightBeResolvableEdges) {
          thereMightBeResolvableEdges = false
          for (e <- edges if e.isResolvable) {
            resCounter += 1
            resolveEdge(e)
            thereMightBeResolvableEdges = true
          }
        }

        nodes.find(n => n.isSplittable) match {
          case Some(splittableNode) => {splitCounter += 1; splitNode(splittableNode)}
          case None =>
        }

        if (edges.forall(e => !e.isResolvable) && nodes.forall(n => !n.isSplittable)) mergeAllSplittedNodes

        if (counter == 129 ) {
          //invariant

          //val gui = new HypergraphVisualizer
          //gui.displayHypergraph(this)
          println(this)

          println("resolvable")
          for (e <- edges) {
            println(e.isResolvable)
          }
          println("splittable")
          for (n <- nodes) {
            println(n.isSplittable)
          }
          
        }
      }
    }

    private def invariant = {
      // Checks if the hypergraph is connected
      var connected = true
      for (n <- nodes) {
        val visitedNodes = new HashSet[Node]
        var nodesToBeVisited = n::Nil
        while (nodesToBeVisited.length > 0) {
          val currentNode = nodesToBeVisited.head
          nodesToBeVisited = nodesToBeVisited.tail
          visitedNodes += currentNode
          for (e <- currentNode.edges; candidateNode <- e.nodes) {
            if (candidateNode != n && !nodesToBeVisited.contains(candidateNode) && !visitedNodes.contains(candidateNode)) {
                nodesToBeVisited = candidateNode::nodesToBeVisited
            }
          }
        }
        if (visitedNodes.size != nodes.size) { connected = false; throw new Exception("Hypergraph has mutually disconnected components") }
      }

      var stuck = true
      if (isTrivial) stuck = false
      for (n <- nodes if n.isSplittable) stuck = false
      for (e <- edges if (e.isResolvable)) stuck = false
      for (e1 <- edges; e2 <- edges if (e2 != e1 && e1.pivot == e2.pivot && e1.nodes == e2.nodes) ) stuck = false
      if (stuck) throw new Exception("Hypergraph simplification is truly stuck")


      if (connected && !stuck) true else false
    }

    val debugResolveEdge = true
    private def resolveEdge(e: Edge) = {
      if (debugResolveEdge) {
        println("RESOLVING EDGE - Begin:")
        println("Edges: " + edges.map(e => e.id))
        println("Resolving Edge: " + e)
      }
      
      val node1 = e.nodesAsSet.head
      val node2 = e.nodesAsSet.last
      deleteEdge(e)
      node1.deleteAllOccurrencesOfEdge(e)
      node2.deleteAllOccurrencesOfEdge(e)
      val resolvedNode = new Node(node1,node2)
      deleteNode(node1)
      deleteNode(node2)
      addNode(resolvedNode)

      if (debugResolveEdge) {
        println("RESOLVING EDGE - Result:")
        println("Edges: " + edges.map(e => e.id))
        println(this)
        println(" ")
      }
    }


    val debugSplitNode = true
    private def splitNode(node: Node) = {
      if (debugSplitNode) {
        println("SPLITTING NODE - Begin:")
        println("Edges: " + edges.map(e => e.id))
        println("Splitting Node: " + node.id + " having edges: " + node.edges.map(e => e.id))
      }

      val nodes = node.split
      for (n <- nodes) {
        addNode(n)
      }
      deleteNode(node)

      if (debugSplitNode) {
        println("SPLITTING NODE - Result:")
        println("Edges: " + edges.map(e => e.id))
        println(this)
        println(" ")
      }
    }

    private def mergeAllSplittedNodes = {
      println("hey!")
      for (e <- edges) {
        //println("EDGE: " + e)
        val (positiveNodes, negativeNodes) = e.partitionByPolarity
        val positiveNodesAsSet = positiveNodes.toSet[Node]
        val negativeNodesAsSet = negativeNodes.toSet[Node]
        //println("PositiveNodes: " + positiveNodesAsSet.map(n => n.id))
        //println("NegativeNodes: " + negativeNodesAsSet.map(n => n.id))
        def mergeIfSplitted(set: scala.collection.immutable.Set[Node]) = if (set.size > 1 && set.forall(n => equalClauses(n.clause, set.head.clause))) {
          println("SPLITTED!!! :" + set.map(n => n.id) )
          val newNode = new Node(set.toList)
          addNode(newNode)
          for (n <- set) deleteNode(n)
        }
        mergeIfSplitted(positiveNodesAsSet)
        mergeIfSplitted(negativeNodesAsSet)
      }
    }
  }
}
