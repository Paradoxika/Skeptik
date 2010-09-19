/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package resolutionproofcompression

import scala.collection.mutable._
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


    private def addEdgeRec(e:Edge, edges: List[Edge]): List[Edge] = edges match {
      case Nil => e::Nil
      case h::tail => if (e > h) e::edges else h::addEdgeRec(e, tail)
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
            println(edgeIndex)
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
    override def toString = {
      var string = "Node " + id  + " (" + proof + "): "
      for (e <- edges) string += e.id + "; "
      string
    }
  }


  class Edge(n: HashSet[Node], a: Atom) extends Ordered[Edge] {
    val nodes = n; val pivot = a; val id = EdgeCounter.get

    def isResolvable: Boolean = {
      if (nodes.size > 2) return false
      else {
        for (n <- nodes; e <- n.edges if (e != this)) {
          if (e.pivot == pivot) return false
        }
        return true
      }
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
    private var mergeableEdges : List[HashSet[Edge]] = Nil
    private var resolvableEdges : List[Edge] = Nil
    private var splittableNodes : List[Node] = Nil

    def isTrivial = {nodes.size == 1}
    def hasAResolvableEdge = {resolvableEdges != Nil}
    def hasASplittableNode = {splittableNodes != Nil}

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
      for (n <- nodes if (n.isSplittable)) {
        println("adding: " + n.id)
        addToSplittableNodes(n)
      }
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
              //if (newEdge.nodes.size == 2) {
              if (true) {
                var isResolvable = true
                if (newEdge.nodes.size != 2) isResolvable = false
                var edgesMergeableWithNewEdge = new HashSet[Edge]
                for (n <- newEdge.nodes; e <- (n.edges) if (newEdge != e)) {
                  if (e.pivot == newEdge.pivot) {
                    isResolvable = false
                    if (e.nodes.size == 2) removeFromResolvableEdges(e)
                    if (newEdge.nodes == e.nodes) edgesMergeableWithNewEdge += e
                  }
                }
                if (isResolvable) addToResolvableEdges(newEdge)
                if (edgesMergeableWithNewEdge.size > 0) addToMergeableEdges(edgesMergeableWithNewEdge, newEdge)
              }
              for (n <- newEdge.nodes) n.addEdge(newEdge)
          }
        }
      }
    }


    def addNode(n:Node) = {nodes += n}
    private def deleteNode(n:Node) = {nodes -= n}

    def addEdge(e:Edge) = {edges += e}
    private def deleteEdge(e:Edge) = {edges -= e}
    //def addEdge(e:Edge) = {edges.update(e.id, e)}
    //private def deleteEdge(e:Edge) = {edges.remove(e.id)}


    private def addToResolvableEdges(e:Edge) = {resolvableEdges = resolvableEdges:::(e::Nil)}
    private def removeFromResolvableEdges(e:Edge) = {resolvableEdges = resolvableEdges.filterNot(edge => e == edge)}

    private def addToSplittableNodes(n:Node) = {splittableNodes = splittableNodes:::(n::Nil)}
    private def removeFromSplittableNodes(n:Node) = {splittableNodes = splittableNodes.filterNot(node => n == node)}
    private def removeFromSplittableNodes(nodes:HashSet[Node]) = {splittableNodes = splittableNodes.filter(node => !nodes.contains(node))}


    private def addToMergeableEdges(S:HashSet[Edge], e:Edge):Unit = {
      mergeableEdges.find(setOfEdges => setOfEdges == S) match {
        case None => addToMergeableEdges(S+e)
        case Some(set) => set += e
      }
    }
    private def addToMergeableEdges(S:HashSet[Edge]):Unit = {mergeableEdges = S::mergeableEdges}

    def simplify = {
      mergeAllMergeableEdges
      var counter = 0
      while (!isTrivial && counter < 10003) {
        counter += 1
        while (hasAResolvableEdge) resolveAResolvableEdge
        if (hasASplittableNode) splitASplittableNode

        if (counter == 10000) {
          println("resolvable")
          for (e <- edges) {
            println(e.isResolvable)
          }
          println("splittable")
          for (n <- nodes) {
            println(n.isSplittable)
          }
          println("mergeable")
          for (e1 <- edges; e2 <- edges if (e2 != e1) ) {
            if (e1.pivot == e2.pivot && e1.nodes == e2.nodes) {
              println(true)
              println(e1)
              println(e2)
            } else println(false)
          }
          println("All Nodes (" + nodes.size + "): " + nodes.map(n => n.id) )
          for (n <- nodes) {
            val visitedNodes = new HashSet[Node]
            var nodesToBeVisited = n::Nil
            while (nodesToBeVisited.length > 0) {
              val currentNode = nodesToBeVisited.head
              nodesToBeVisited = nodesToBeVisited.tail
              visitedNodes += currentNode
              for (e <- currentNode.edges) {
                for (candidateNode <- e.nodes) {
                  if (candidateNode != n && !nodesToBeVisited.contains(candidateNode) && !visitedNodes.contains(candidateNode)) {
                    nodesToBeVisited = candidateNode::nodesToBeVisited
                  }
                }
              }
            }
            println("Reachable from node " + n.id + " (" + visitedNodes.size + "): " + visitedNodes.map(node => node.id))
          }
        }
      }
    }

    private def mergeAllMergeableEdges = {
      println("MERGING EDGES - Begin:")
      println("Edges: " + edges.map(e => e.id))
      println("Mergeable Edges: " + mergeableEdges.map(s => s.map(e => e.id)))
      println("Resolvable Edges: " + resolvableEdges.map(e => e.id))
      println("Splittable Nodes: " + splittableNodes.map(n => n.id))
      val affectedNodes = new HashSet[Node]
      for (M <- mergeableEdges) {
        val newMergedEdge = new Edge(M.head.nodes, M.head.pivot)
        for (e <- M) {
          deleteEdge(e) ; for (n <- e.nodes) n.deleteEdge(e)
        }
        addEdge(newMergedEdge) ; for (n <- newMergedEdge.nodes) n.addEdge(newMergedEdge)
        if (newMergedEdge.isResolvable) addToResolvableEdges(newMergedEdge)
        affectedNodes ++= newMergedEdge.nodes
      }
      val (splittableAffectedNodes, nonSplittableAffectedNodes) = affectedNodes.partition(n => n.isSplittable)
      for (n <- splittableAffectedNodes) if (!splittableNodes.contains(n)) addToSplittableNodes(n)
      removeFromSplittableNodes(nonSplittableAffectedNodes)
      mergeableEdges = Nil  //Resets the mergeableEdges list
      println("MERGING EDGES - Result:")
      println("Edges: " + edges.map(e => e.id))
      println("Mergeable Edges: " + mergeableEdges.map(s => s.map(e => e.id)))
      println("Resolvable Edges: " + resolvableEdges.map(e => e.id))
      println("Splittable Nodes: " + splittableNodes.map(n => n.id))
      println(this)
    }

    private def resolveAResolvableEdge = {
      println("RESOLVING EDGE - Begin:")
      println("Edges: " + edges.map(e => e.id))
      println("Mergeable Edges: " + mergeableEdges.map(s => s.map(e => e.id)))
      println("Resolvable Edges: " + resolvableEdges.map(e => e.id))
      println("Splittable Nodes: " + splittableNodes.map(n => n.id))
      val chosenEdge = resolvableEdges.head
      println("Resolving Edge: " + chosenEdge.id)
      resolvableEdges = resolvableEdges.tail
      val node1 = chosenEdge.nodes.head
      val node2 = chosenEdge.nodes.last
      deleteEdge(chosenEdge)
      println("Edges: " + edges.map(e => e.id))
      node1.deleteEdge(chosenEdge)
      node2.deleteEdge(chosenEdge)
      val resolvedNode = new Node(node1,node2)
      deleteNode(node1)
      deleteNode(node2)
      removeFromSplittableNodes(node1)
      removeFromSplittableNodes(node2)
      addNode(resolvedNode)
      updateMergeableEdges(resolvedNode)
      if (resolvedNode.isSplittable) addToSplittableNodes(resolvedNode)
      if (mergeableEdges != Nil) mergeAllMergeableEdges
      println("RESOLVING EDGE - Result:")
      println("Edges: " + edges.map(e => e.id))
      println("Mergeable Edges: " + mergeableEdges.map(s => s.map(e => e.id)))
      println("Resolvable Edges: " + resolvableEdges.map(e => e.id))
      println("Splittable Nodes: " + splittableNodes.map(n => n.id))
      println(this)
      println(" ")
    }

    private def splitASplittableNode = {
      // require( mergeableEdges == Nil ) // Arbitrary splitting of splittable nodes could make some edges unmergeable. This function does not take care of this. That is why it should only be called when mergeableEdges is empty.
      println("SPLITTING NODE - Begin:")
      println("Edges: " + edges.map(e => e.id))
      println("Mergeable Edges: " + mergeableEdges.map(s => s.map(e => e.id)))
      println("Resolvable Edges: " + resolvableEdges.map(e => e.id))
      println("Splittable Nodes: " + splittableNodes.map(n => n.id))
      val chosenNode = splittableNodes.head
      println("Splitting Node: " + chosenNode.id)
      splittableNodes = splittableNodes.tail
      val nodes = chosenNode.split
      for (n <- nodes) {
        addNode(n)
        for (e <- n.edges if (e.isResolvable)) addToResolvableEdges(e)
      }
      deleteNode(chosenNode)
      println("SPLITTING NODE - Result:")
      println("Edges: " + edges.map(e => e.id))
      println("Mergeable Edges: " + mergeableEdges.map(s => s.map(e => e.id)))
      println("Resolvable Edges: " + resolvableEdges.map(e => e.id))
      println("Splittable Nodes: " + splittableNodes.map(n => n.id))
      println(this)
      println(" ")
    }

    private def updateMergeableEdges(newNode: Node) = {
      // require( mergeableEdges == Nil ) // Otherwise, updating mergeableEdges would be much more complicated.
      val edgesAlreadyInMergeableSet = new HashSet[Edge]
      //for (edge <- newNode.edges if edge.nodes.size == 2) {
      for (edge <- newNode.edges) {
        if (!edge.isResolvable) removeFromResolvableEdges(edge)
        else if (!resolvableEdges.contains(edge)) addToResolvableEdges(edge)
        if (!edgesAlreadyInMergeableSet.contains(edge)) {
          val edgesMergeableWithCurrentEdge = new HashSet[Edge]
          for (e <- (newNode.edges) if (edge != e)) {
            if (e.pivot == edge.pivot && e.nodes == edge.nodes) {
              edgesMergeableWithCurrentEdge += e
              edgesAlreadyInMergeableSet += e
            }
          }
          if (edgesMergeableWithCurrentEdge.size > 0) {
            addToMergeableEdges(edgesMergeableWithCurrentEdge + edge)
          }
        }
      }
    }
  }


}
