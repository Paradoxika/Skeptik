package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.dijkstra._

object FibonacciTest {
  def main2(args: Array[String]):Unit = {
    val heap = new FibonacciHeap[String,Int](Integer.MIN_VALUE)
    
    heap.insert("a", 1)
    
    heap.insert("b", 2)
    
    heap.insert("c", 3)
    
    println(heap)
    
    val m = heap.extractMin
    
    println("min: " + m)
    
    println(heap)
    
    val m2 = heap.extractMin
    
    println("last heap: "+ heap)
  }
  
    def main(args : Array[String]) : Unit = {
     //val heap = new FibonacciHeap[int](Int.MinValue);
     val heap = new FibonacciHeap[String,Int](Int.MinValue);
     heap.insert("f",10)
     heap.insert("l",98)
     heap.insert("d",5)
     heap.insert("m",123)
     heap.insert("b",3)
     heap.insert("i",52)
     heap.insert("j",52)
     heap.insert("k",52)
     heap.insert("h",34)
     heap.insert("a",1)
     heap.insert("g",22)
     heap.insert("c",4)
     heap.insert("e",6)
     
     println(heap)
     
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
    heap.decreaseKey("m",29)
//    val m = heap.min.get
//    println(m.toString(true))
//    println(m.asSequence())
//    println(m.right.right.child.get.right)
//    println(m.right.right.child.get.right.child)
//    heap.printSpecial
          println(heap)
          
     println("min: " + heap.extractMin)
          println(heap)
     heap.delete("j")
//          println(heap)

     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
     println("min: " + heap.extractMin)
          println(heap)
        
  }
}