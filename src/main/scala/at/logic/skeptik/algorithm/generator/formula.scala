package at.logic.skeptik.algorithm.generator

import at.logic.skeptik.expression._
import at.logic.skeptik.expression.formula.{Imp, enrichFormula}
import collection.mutable.{HashSet => MSet}
import util.Random

object FormulaGenerator {
  private val atoms = Seq("A","B","C","D","E","F","G","H","I","J",
                          "K","L","M","N","O","P","Q","R","S","T",
                          "U","V","X","Y","W","Z").map(_.^(o))
 
  
  def generateExample(n: Int): E = {
    val a = "A"^o
    val b = "B"^o
    def t(k: Int)(e: E): E = 
      if (k == 0) e
      else Imp(Imp(t(k-1)(e), ("C"+k)^o ), ("D"+k)^o)  
    val tn = t(n) _
    
    (a → b) → (tn(a) → tn(b))
  }
  
  def generateOne(length: Int, numOfSymbols: Int):E = {
    val r = new Random()
    
    def growRandomList(list: List[E]): List[E] = {   
      val numOfSymbolsInList = list.distinct.length
      val index = if (numOfSymbolsInList == numOfSymbols) r.nextInt(numOfSymbols)
                  else if (numOfSymbols - numOfSymbolsInList == length - list.length) numOfSymbolsInList
                  else r.nextInt(numOfSymbolsInList + 1)
      atoms(index)::list        
    }

    def generateRandomList(length: Int, numOfSymbols: Int):List[E] = { 
      def rec(i:Int):List[E] = {
        if (i == 1) List("A"^o)
        else {
          val previous = rec(i-1)
          growRandomList(previous)
        }
      }
      rec(length)
    }
    
    def generateRandomList2(length: Int, numOfSymbols: Int):List[E] = { 
      (for (i <- 1 to length) yield atoms(r.nextInt(numOfSymbols))).toList
    }
    def generateRandomFormula(l:List[E]):E = {
      if (l.length == 1) l.head
      else {
        //println(l)
        //println(l.length)
        val i = r.nextInt(l.length-1) + 1
        //println(i)
        val left = generateRandomFormula(l.take(i))
        val right = generateRandomFormula(l.drop(i))
        Imp(left,right)
      }
    }
    generateRandomFormula(generateRandomList(length, numOfSymbols))
  }
  
  def generateAll(length: Int, numOfSymbols: Int) = {
    
    def growLists(lists: Seq[List[E]]) = (for (l <- lists) yield {
      val numOfSymbolsInList = l.distinct.length
      val numOfSymbolsToTake = if (numOfSymbolsInList < numOfSymbols) numOfSymbolsInList + 1 else numOfSymbols
      for (a <- atoms.take(numOfSymbolsToTake).view) yield a::l        
    }).flatten.filter(l => numOfSymbols - l.distinct.length <= length - l.length)
    
    val lists = {
      def rec(i:Int):Seq[List[E]] = {
        if (i == 1) Seq(List("A"^o))
        else {
          val previous = rec(i-1)
          growLists(previous)
        }
      }
      rec(length)
    }
    
    def generateFormulas(l:List[E]): Seq[E] = {
      var formulas = List[E]()
      if (l.length == 1) formulas = l
      else for (i <- 1 to l.length - 1) {
        val left = l.take(i)
        val right = l.drop(i)
        val leftFormulas = generateFormulas(left)
        val rightFormulas = generateFormulas(right)
        for (lf <- leftFormulas; rf <- rightFormulas) formulas = Imp(lf,rf)::formulas
      }
      formulas
    } 
    
    var formulas = Seq[E]()
    for (l <- lists) formulas ++= generateFormulas(l)
    
    formulas
  }
  
  
  def generateAllRelaxed(length: Int, nSymbols: Int): Set[E] = {
    if (length == 1) atoms.take(nSymbols).toSet
    else {
      var formulas = new MSet[E]()
      for (i <- 1 to length-1) {
        val leftFormulas = generateAllRelaxed(i, nSymbols)
        val rightFormulas = generateAllRelaxed(length - i, nSymbols)
        for (lf <- leftFormulas; rf <- rightFormulas) formulas += Imp(lf,rf)
      }  
      formulas.toSet
    }
  }
  
}