package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.{HashMap => MMap}
import scala.annotation.tailrec

class FibonacciHeap[T1,T2 <% Ordered[T2]](absoluteMin: T2)
    extends MyPriorityQueue[T1,T2] {
  
//  println("new heap")
  
  var min: Option[FNode] = None
  var n: Int = 0
  val nodeMap = MMap[T1,FNode]()
  
  def correctlyChained(node: FNode): Boolean = {
    node.left.right == node && node.right.left == node
  }
  
  def addToRoot(node: FNode) = {
    node.parent = None
    node.remove
    min match {
      case None => min = {
        node.left = node
        node.right = node
        Some(node)
      }
      case Some(m) => {
        m.addLeft(node)
        if (m.key > node.key) min = Some(node)
      }
    }
    require(node.left.right == node && node.right.left == node)
  }
  
  def addNodeMap(elem: T1, newNode: FNode) = nodeMap += (elem -> newNode)
  
  def insert(elem: T1, key: T2) = {
    if (!nodeMap.isDefinedAt(elem)) {
      val newNode = new FNode(elem,key)
      addNodeMap(elem,newNode)
      addToRoot(newNode)
      n = n + 1
    }
  }
  
  def minimum: Option[T1] = min match {
    case None => None
    case Some(node) => Some(node.element) 
  }
  
//  def addAllChildToRoot(node: FNode) {
//     node.child.foreach(ch => {
//      var nextChild = ch.right
//      while (nextChild != ch) {
//        val thisChild = nextChild
//        nextChild = nextChild.right
//        addToRoot(thisChild)
//      }
//      addToRoot(ch)
//    })
//  }
  
  def addAllChildToRoot(node: FNode) {
     node.child.foreach(_.asSequence().foreach(ch => {
      addToRoot(ch)
    }))
  }
  
  def extractMin: Option[T1] = min match {
    case None => None
    case Some(minNode) => {
      nodeMap -= (minNode.element)
//      if (deleted.contains(minNode)) println("extracting deleted: " + minNode)
      addAllChildToRoot(minNode)
      val r = minNode.right
      minNode.remove
      if (r == minNode) min = None //Now empty      
      else {
        min = Some(r)
        consolidate
      }
      n = n - 1
//      if (min.isDefined) println((correctlyChained(min.get) && correctlyChained(minNode) && correctlyChained(min.get.left)) + " " + min.get.toString(true) + " " + min.get.left.toString(true) + " " + minNode.toString(true))
//      else println("empty")
      Some(minNode.element)
    }
  }
  
  def consolidate = min match {
    case None => 
    case Some (minNode) => {
//      val dN = 2*Math.log(n).toInt+1
//      val dN = n // log(n) should suffice
//      val A = new Array[FNode](dN)
      val A = MMap[Int,FNode]()
      val rootSeq = minNode.asSequence()
      rootSeq.foreach(node => {
//      var node = minNode.right
//      while(node != minNode) {
//        val nextNode = node.right
//        println(node + " ~ " + minNode)
        var x = node
        var d = x.degree
//        println(x + " degree " + d)
        var dNode = x
        while (A.isDefinedAt(d)) {
          var y = A(d)
          if (x.key > y.key) {
            val xy = y
            y = x
            x = xy
          }
//          println("link " + y + " to " + x)
          link(y,x)
          A -= d
          if (d+1 < A.size) d = d + 1
        }
        
        A+=(d -> x)
//        node = nextNode
//        println("A after " + x + " ::: " + A.mkString(","))
      })
      min = None
//      println("A: " + A.mkString(","))
      A.values.foreach(node => {
//        println("remain: " + node)
        addToRoot(node)
      })
    }
  }
  
  def link(child: FNode, parent: FNode) = {
    child.remove
    parent.addChild(child)
    parent.degree = parent.degree + 1
    child.marked = false
//    println("child: " + child.toString(true))
//    println("parent: " + parent.toString(true))
  }
  
  def accessNodeMap(elem: T1) = nodeMap.get(elem)
  
  def decreaseKey(elem: T1, value: T2) {
    accessNodeMap(elem) match {
      
      case Some(elemNode) if (elemNode.key > value) => { //otherwise current value is already smaller
        
        elemNode.key = value
        elemNode.parent match {
          
          case Some(y) if (y.key > value) => {
            
//            println("parent of " + elemNode + " is " + y)
//            println("at this point child of " + special + " = " + special.child)
            cut(elemNode,y)
            
            cascading_cut(y)
          }
          case Some(y) => // println(y + " < " + elemNode)
          case None => 
        }
      }
      case Some(elemNode) => //println(elemNode + " < " + value)
      case None => 
    }
    min match {
      case Some(m) if (m.key > value) => {
        
        min = accessNodeMap(elem)
      }
      case _ => 
    }
//    println(min)
//    println(nodeMap.map(n => n._1 + " ch: " + n._2.child).mkString(","))
//    println(nodeMap.map(n => n._1 + " parent: " + n._2.parent).mkString(","))
//    println(nodeMap.map(n => n._1 + " left: " + n._2.left).mkString(","))
//    println(nodeMap.map(n => n._1 + " right: " + n._2.right).mkString(","))
  }
  
  def cut(x: FNode, y: FNode) = {
    y.removeChild(x)
    addToRoot(x)
//    println("after adding " + x + " to root: " + x.toString(true))
    x.marked = false
    y.degree = y.degree - 1
//    println("after cut child of " + special + " = " + special.child)
  }
  
  def cascading_cut(y: FNode): Unit = {
    y.parent match {
      case None =>
      case Some(z) => {
        if (y.marked == false) y.marked = true
        else {
          cut(y,z)
          cascading_cut(z)
        }
      }
    }
//    println("after cascadind cut child of " + special + " = " + special.child)
  }
  
  def delete(elem: T1) = accessNodeMap(elem) match {
    case None =>
    case Some(node) => {
      decreaseKey(elem, absoluteMin)
      extractMin
    }
  }
  
  def isEmpty: Boolean = !min.isDefined

  override def toString() : String = {
    var str = "HEAP"
    min match {
      case None => {
        str = str.concat(" EMPTY "); return str
      }
      case Some(minNode) => {
        str =str.concat("\n-").concat("min " + minNode.toTreeString("\t",1))
        minNode.asSequence().foreach({sib =>
          if (sib != minNode) str =str.concat("\n-").concat(sib.toTreeString("\t",1))
        })
        str
      }
    }
  }

  
  class FNode(val element: T1, keyIn: T2) {
    var key: T2 = keyIn
    var degree: Int = 0
    var parent: Option[FNode] = None
    var child: Option[FNode] = None
    var left:FNode = this
    var right:FNode = this
    var marked: Boolean = false
    
    def unparent = {
      parent = None
    }
    
    def remove = { // y <-> x <-> z ~~> y <-> z
      val x = this
      val y = x.left
      val z = x.right
//      x.parent = None
//      x.child = None
      y.right = z
      z.left = y
      x.left = x
      x.right = x
      if (!correctlyChained(y)) {
        println("y: " + y.toString(true))
      }
//      if (!correctlyChained(x)) {
//        println("x: " + x.toString(true))
//      }
      if (!correctlyChained(z)) {
        println("z: " + z.toString(true))
      }
      require(correctlyChained(y) && correctlyChained(z)  && correctlyChained(x))
//      println("removing " + this)
//      println("resulting left " + y.toString(true))
//      println("resulting right " + z.toString(true))
    }
    
    def removeChild(that: FNode) = child match {
      case None => 
      case Some(ch) => {
        if (that.right == that) this.child = None
        else this.child = {
          Some(that.right)
        }
      }
      that.remove
    }
    
    def addChild(that: FNode) = {
//      println("adding " + that + " to " + this)
//      println("that's 1st child: " + that.child)
//      println(this + " gets child: " + that)
      that.left = that
      that.right = that
      that.parent = Some(this)
      child match {
        case None => child = {
          Some(that)
        }
        case Some(firstChild) => {
          that.remove
          firstChild.addLeft(that)
        }
      }
//      println("after adding " + that + " to " + this + " its child: " + this.child.get.toString(true))
    }
    
    def addLeft(that: FNode) = { //y <-> x ~~> y <-> z <-> x
      val x = this
      val y = left
      val z = that
      y.right = z
      z.left = y
      x.left = z
      z.right = x
//      println("after adding " + that + " to " + this + ": " + this.toString(true))
    }
    
    def addRight(that: FNode) = { //x <-> y ~~> x <-> z <-> y
      val x = this
      val y = right
      val z = that
      x.right = z
      z.left = x
      y.left = z
      z.right = y
    }
    
    @tailrec
    final def asSequence(initSeq: List[FNode] = List()): List[FNode] = {
      require(this == left.right && this == right.left)
//      println("here in asSequence for " + this + " m: " + min)
      if (initSeq.size > 0) {
//        println(this.left + " <-> " + this + " <-> " + this.right + " iSH: "+ initSeq.head)
        if (initSeq.last == this) initSeq
        else right.asSequence(initSeq.::(this))
      }
      else right.asSequence(List(this))
    }
    
    def toString(neighbours: Boolean) = {
      if (neighbours) this.left + " <-> " + this + " <-> " + this.right
      else this
    }
    
    override def toString = {
      element.toString// + "~" + key // + " " + marked
    }
    
    def toTreeString(indent:String,indentLevel:Int) : String = {
      var indentStr = indent
      for(i <- 1 to indentLevel) indentStr = indentStr.concat(indent)
      
      var str = indentStr.concat(this.toString)
      child.foreach(c => c.asSequence().foreach(child => {
        require(child == child.right.left && child == child.left.right)
        str = str.concat("\n").concat(child.toTreeString(indent,indentLevel+1))
      }))
      str
    }
  }
}