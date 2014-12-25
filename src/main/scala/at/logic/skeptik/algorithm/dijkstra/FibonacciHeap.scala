package at.logic.skeptik.algorithm.dijkstra

import scala.collection.mutable.ListBuffer
import scala.collection.mutable.{HashMap => MMap}
import scala.annotation.tailrec

class FibonacciHeap[T1,T2 <% Ordered[T2]](absoluteMin: T2)
    extends MyPriorityQueue[T1,T2] {

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
  
  def addAllChildToRoot(node: FNode) {
     node.child.foreach(_.asSequence().foreach(ch => {
      addToRoot(ch)
    }))
  }
  
  def extractMin: Option[T1] = min match {
    case None => None
    case Some(minNode) => {
      nodeMap -= (minNode.element)
      addAllChildToRoot(minNode)
      val r = minNode.right
      minNode.remove
      if (r == minNode) min = None //Now empty      
      else {
        min = Some(r)
        consolidate
      }
      n = n - 1
      Some(minNode.element)
    }
  }
  
  def consolidate = min match {
    case None => 
    case Some (minNode) => {
      val A = MMap[Int,FNode]()
      val rootSeq = minNode.asSequence()
      rootSeq.foreach(node => {
        var x = node
        var d = x.degree
        var dNode = x
        while (A.isDefinedAt(d)) {
          var y = A(d)
          if (x.key > y.key) {
            val xy = y
            y = x
            x = xy
          }
          link(y,x)
          A -= d
          if (d+1 < A.size) d = d + 1
        }
        
        A+=(d -> x)
      })
      min = None
      A.values.foreach(node => {
        addToRoot(node)
      })
    }
  }
  
  def link(child: FNode, parent: FNode) = {
    child.remove
    parent.addChild(child)
    parent.degree = parent.degree + 1
    child.marked = false
  }
  
  def accessNodeMap(elem: T1) = nodeMap.get(elem)
  
  def decreaseKey(elem: T1, value: T2) {
    accessNodeMap(elem) match {
      
      case Some(elemNode) if (elemNode.key > value) => { //otherwise current value is already smaller
        
        elemNode.key = value
        elemNode.parent match {
          
          case Some(y) if (y.key > value) => {
            cut(elemNode,y)
            
            cascading_cut(y)
          }
          case Some(y) =>
          case None => 
        }
      }
      case Some(elemNode) =>
      case None => 
    }
    min match {
      case Some(m) if (m.key > value) => {
        
        min = accessNodeMap(elem)
      }
      case _ => 
    }
  }
  
  def cut(x: FNode, y: FNode) = {
    y.removeChild(x)
    addToRoot(x)
    x.marked = false
    y.degree = y.degree - 1
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
      y.right = z
      z.left = y
      x.left = x
      x.right = x
      if (!correctlyChained(y)) {
        println("y: " + y.toString(true))
      }
      if (!correctlyChained(z)) {
        println("z: " + z.toString(true))
      }
      require(correctlyChained(y) && correctlyChained(z)  && correctlyChained(x))
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
    }
    
    def addLeft(that: FNode) = { //y <-> x ~~> y <-> z <-> x
      val x = this
      val y = left
      val z = that
      y.right = z
      z.left = y
      x.left = z
      z.right = x
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
      if (initSeq.size > 0) {
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