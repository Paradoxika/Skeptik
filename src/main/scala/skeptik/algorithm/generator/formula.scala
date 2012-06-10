package skeptik.algorithm.generator

import skeptik.expression._
import skeptik.expression.formula._

object formulaGen {
  
  //def generate(quantity: Int) = for (i <- 1 until quantity+1) yield Prop("P"+i)
  def generate(quantity: Int) = Seq("A","B","C","D","E","F","G","H","I","J","K").map(Prop(_)).take(quantity)
    
  def generate(expSeq: Seq[E], depth: Int): Seq[E] = {
    val exps = if (depth == 1) expSeq else generate(expSeq, depth - 1)
    (for (f1 <- exps.par; f2 <- exps.par) yield Imp(f1,f2)).seq
  }

  def generateAcc(expSeq: Seq[E], depth: Int): Seq[E] = {
    val exps = if (depth == 1) expSeq else generateAcc(expSeq, depth - 1)
    expSeq ++ (for (f1 <- exps.par; f2 <- exps.par) yield Imp(f1,f2)).seq
  }
  
  def generate2(depth: Int, vars: Int):Seq[E] = {
    //import scala.collection.mutable.{HashSet => MSet}
    class Tree
    case class L() extends Tree
    case class N(l:Tree,r:Tree) extends Tree 
    
    println("hi!")
    
    var trees : Seq[Tree] = Seq()
    def generateTrees(d: Int):Unit = {
      //println(d)
      //println(trees)
      if (d == 0) {
        trees = L() +: trees
        //println("trees: " + trees)
      }
      else {
        generateTrees(d-1)
        val treesAux : Seq[Tree] = Seq() ++ trees
        for (t1 <- treesAux; t2 <- treesAux) {
          trees = N(t1,t2) +: trees
          //println(trees)
        }
      }
    }
    
    def mapTreeToExpressions(tree:Tree): Seq[E] = {
      //println(tree)
      val atoms = generate(vars)
      var counter = 0
      def getAtoms() = {
        counter += 1
        atoms.take(counter)    
      }
      
      def rec(t:Tree): Seq[E] = t match {
        case L() => getAtoms()
        case N(t1,t2) => for (e1 <- rec(t1); e2 <- rec(t2)) yield Imp(e1,e2)
      }
      val exps = rec(tree)
      println(exps)
      exps
    }
    
    println("hi2")
    generateTrees(depth)
    println("hi3")
    //println(trees)
    trees.map(mapTreeToExpressions).toSeq.flatten
  }
}