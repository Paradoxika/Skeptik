/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

import scala.collection.mutable._
//import scala.collection.immutable._
import resolutionproofcompression.Utilities._
import resolutionproofcompression.ResolutionCalculus._

object Hypergraph {
  val EdgeCounter = new Counter
  val NodeCounter = new Counter

  class Node(p: ResolutionProof, c: Clause) {
    val proof: ResolutionProof = p
    val clause: Clause = c
    val id: Int = NodeCounter.get

    private var edgesContainingThisNode: List[Edge] = Nil
    def edges : List[Edge] = edgesContainingThisNode.toList
    def addEdge(e:Edge) = {
      edgesContainingThisNode = addEdgeRec(e, edgesContainingThisNode) // edges are sorted first by pivot and then by id.
    }
    private def addEdgeRec(e:Edge, edges: List[Edge]): List[Edge] = edges match {
      case Nil => e::Nil
      case h::tail => if (e > h) e::edges else h::addEdgeRec(e, tail)
    }

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
        e.nodes -= n1
        e.nodes += this
      }
      for (e <- n2.edges) {
        e.nodes -= n2
        e.nodes += this
      }
      edgesContainingThisNode = merge(n1.edges,n2.edges) // merges in a sorted way and removes duplicates
    }
    def this(nodesToBeMerged:List[Node]) = {
      this(argmin(nodesToBeMerged.map(n => n.proof).toList, proofLength)._1,nodesToBeMerged.head.clause)
      for (n <- nodesToBeMerged; e <- n.edges) {
        e.nodes -= n
        e.nodes += this
      }
      val edgesOfEachNode = nodesToBeMerged.map(n => n.edges).toList
      edgesContainingThisNode = merge(edgesOfEachNode)
    }
    private def merge(list1: List[Edge],list2: List[Edge]): List[Edge] = {
      (list1, list2) match {
        case (Nil, _) => list2
        case (_, Nil) => list1
        case (h1::t1, h2::t2) => {
          if (h1.id == h2.id) h1::merge(t1,t2)
          else if (h1 > h2) h1 :: merge(t1, list2)
          else h2 :: merge(list1, t2)
        }
      }
    }
    private def merge(listOfListsOfEdges: List[List[Edge]]): List[Edge] = {
      val emptyList: List[Edge] = Nil
      (listOfListsOfEdges :\ emptyList)(merge)
    }



    def deleteEdge(e:Edge) = {edgesContainingThisNode = edgesContainingThisNode.filterNot(edge => edge == e)}
    def isSplittable: Boolean = (1 < gcd(edgesGroupedByPivot.map(l => l.length)))

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
            e.nodes -= this
            e.nodes += n
            n.addEdge(e)
          }
          edgeGroupIndex += 1
        }
        nodeIndex += 1
      }
      newNodes.toList
    }

    def isNeighbourOf(that: Node, e: Edge) = {
      val (positiveNodes, negativeNodes) = e.partitionByPolarity
      (positiveNodes.contains(this) && negativeNodes.contains(that)) || (positiveNodes.contains(that) && negativeNodes.contains(this))
    }

    def neighbours : scala.collection.immutable.Set[(Node,Edge)] = {
      val neighboursSeq = for (e <- edges; n <- e.nodes if isNeighbourOf(n,e) ) yield (n,e)
      return neighboursSeq.toSet
    }

    override def toString = {
      var string = "Node " + id  + " (" + clause + "): " + " (" + proof + "): "
      for (e <- edges) string += e.id + "; "
      string
    }
  }


  class Edge(n: HashSet[Node], a: Atom) extends Ordered[Edge] {
    val nodes = n; val pivot = a; val id = EdgeCounter.get

    def partitionByPolarity: (HashSet[Node], HashSet[Node]) = {
      var positiveNodes = new HashSet[Node]
      var negativeNodes = new HashSet[Node]
      for (n <- nodes) {
        if (n.clause.exists(lit => lit.atom == pivot && lit.polarity == true)) positiveNodes += n
        else negativeNodes += n
      }
      return (positiveNodes,negativeNodes)
    }

    def isResolvable: Boolean = {
      if (false) {
        println("Is Edge " + id + " resolvable?")
        println("Neighbours of Node " + nodes.head.id + ":" + nodes.head.neighbours.map(neigh => neigh._1.id))
        println("Neighbours of Node " + nodes.last.id + ":" + nodes.last.neighbours.map(neigh => neigh._1.id))
        println(nodes.size == 2)
        println((nodes.forall(n => (n.edges.forall(e => e == this || e.pivot != pivot)))))
        //println(isTriangleSafe)
      }

      def isTriangleSafe: Boolean = {
        val n1 = nodes.head
        val n2 = nodes.last
        for ((n1N,e1) <- n1.neighbours) {
          for ((n2N,e2) <- n2.neighbours if n2N == n1N) {
            if (false) {
              println()
              println((e1,e2))
              println(e1 != e2)
              println(e1.pivot == e2.pivot)
            }
            if (e1 != e2 && e1.pivot == e2.pivot) {return false}
          }
        }
        //println("triangle safe")
        return true
      }
      (nodes.size == 2) && (nodes.forall(n => (n.edges.forall(e => e == this || e.pivot != pivot)))) && isTriangleSafe
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
      val hashMapClauseToNode = new HashMap[Clause,Node]
      buildResolutionHypergraphRec(proof, visitedProofs, hashMapClauseToNode)
    }
    private def buildResolutionHypergraphRec(proof: ResolutionProof,
                                     visitedProofs: HashSet[ResolutionProof],
                                     hashMapClauseToNode: HashMap[Clause, Node]) : Unit = {
      if (!visitedProofs.contains(proof)) {
        visitedProofs += proof
        proof match {
          case Input(c) => {
              val newNode = new Node(proof, c)
              hashMapClauseToNode += ( c -> newNode )
              addNode(newNode)
          }
          case Resolvent(left, right) => {
              buildResolutionHypergraphRec(left,visitedProofs, hashMapClauseToNode)
              buildResolutionHypergraphRec(right,visitedProofs, hashMapClauseToNode)

              val (leftPivot,rightPivot) = proof.asInstanceOf[Resolvent].pivot
              val leftNodes = leftPivot.ancestorInputClauses.map(c => hashMapClauseToNode(c))
              val rightNodes = rightPivot.ancestorInputClauses.map(c => hashMapClauseToNode(c))
              val newEdge = new Edge((new HashSet[Node] ++ leftNodes) ++ rightNodes, leftPivot.atom)
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
      //mergeAllMergeableEdges
      var counter = 0
      var resCounter = 0
      var splitCounter = 0
      while (!isTrivial && counter < 13) {
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

        if (counter == 12 ) {
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


//      def hasTautologicalCycle : Boolean = {
//        for (n <- nodes) if (hasTautologicalCycleRec(n,n,new HashSet[Node],Nil)) return true
//        return false
//      }
//      def hasTautologicalCycleRec(initialNode: Node, currentNode:Node, visitedNodes:HashSet[Node], path:List[Atom]) : Boolean = {
//        if (visitedNodes.contains(currentNode)) return false
//        else {
//          if (currentNode.id == initialNode.id) {
//            throw new Exception("Hypergraph has tautological cycles.")
//            return true
//          }
//          for (e <- currentNode.edges if !path.contains(e.pivot); n <- e.nodes if n.id != currentNode.id && !visitedNodes.contains(n)) {
//            if (hasTautologicalCycleRec(initialNode,n,visitedNodes+currentNode,e.pivot::path)) return true
//          }
//          return false
//        }
//      }


      var stuck = true
      if (isTrivial) stuck = false
      for (n <- nodes if n.isSplittable) stuck = false
      for (e <- edges if (e.isResolvable)) stuck = false
      for (e1 <- edges; e2 <- edges if (e2 != e1 && e1.pivot == e2.pivot && e1.nodes == e2.nodes) ) stuck = false
      if (stuck) throw new Exception("Hypergraph simplification is truly stuck")


      if (connected && !stuck) true else false
    }

    private def resolveEdge(e: Edge) = {
//      println("RESOLVING EDGE - Begin:")
//      println("Edges: " + edges.map(e => e.id))
//      println("Resolving Edge: " + e)
      val node1 = e.nodes.head
      val node2 = e.nodes.last
      deleteEdge(e)
      node1.deleteEdge(e)
      node2.deleteEdge(e)
      val resolvedNode = new Node(node1,node2)
      deleteNode(node1)
      deleteNode(node2)
      addNode(resolvedNode)
//      println("RESOLVING EDGE - Result:")
//      println("Edges: " + edges.map(e => e.id))
//      println(this)
//      println(" ")
      //require(invariant)
    }



    private def splitNode(node: Node) = {
      // require( mergeableEdges == Nil ) // Arbitrary splitting of splittable nodes could make some edges unmergeable. This function does not take care of this. That is why it should only be called when mergeableEdges is empty.
//      println("SPLITTING NODE - Begin:")
//      println("Edges: " + edges.map(e => e.id))
//      println("Splitting Node: " + node.id)
      val nodes = node.split
      for (n <- nodes) {
        addNode(n)
      }
      deleteNode(node)
//      println("SPLITTING NODE - Result:")
//      println("Edges: " + edges.map(e => e.id))
//      //println(this)
//      println(" ")
      //require(invariant)
    }
  }
}
