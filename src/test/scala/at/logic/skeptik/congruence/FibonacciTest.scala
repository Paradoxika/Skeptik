package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.dijkstra._
import scala.util.Random
import at.logic.skeptik.util.io.FileOutput
import java.io.File

object FibonacciTest {
  def main(args : Array[String]) : Unit = {
    val file = new FileOutput("experiments/congruence/fibVsArray2.csv")
    file.write("length,fibonacci,array\n")
    
    
    val random = new Random
    val gamma = 3
    val max = 1000000
    for (testlength <- 1 to max) {
      file.write(testlength+",")
      val fibTimebefore = System.currentTimeMillis()
      val fibonacci = new FibonacciHeap[Int,Int](Int.MinValue);
      for (i <- 0 to (testlength-1)) {
        val value = random.nextInt(testlength)
        fibonacci.insert(i, value)
        val decrease = random.nextInt(10)
        if (decrease < gamma && i > 0) {
          val toDec = random.nextInt(i)
          if (toDec == -1 ) println("-1 found!")
          val to = random.nextInt(testlength)
          fibonacci.decreaseKey(toDec, to)
        }
        else if(gamma <= decrease && decrease < 2*gamma) {
          fibonacci.extractMin
        }
      }
      val fibSpeed = System.currentTimeMillis() - fibTimebefore
//      println("Fibonacci time: " + fibSpeed)
      file.write(fibSpeed+",")
      val arrayTimebefore = System.currentTimeMillis()
      val array = new ArrayPQ[Int,Int]
      for (i <- 0 to (testlength-1)) {
        val value = random.nextInt(testlength)
        array.insert(i, value)
        val decrease = random.nextInt(10)
        if (decrease < gamma && i > 0) {
          val toDec = random.nextInt(i)
          if (toDec == -1 ) println("-1 found!")
          val to = random.nextInt(testlength)
          array.decreaseKey(toDec, to)
        }
        else if(gamma <= decrease && decrease < 2*gamma) {
          array.extractMin
        }
      }
      val arraySpeed = System.currentTimeMillis() - arrayTimebefore
      file.write(arraySpeed+"\n")
//      println("Array time: " + arraySpeed)
    }
    
    
    
  }
  def main2(args : Array[String]) : Unit = {
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