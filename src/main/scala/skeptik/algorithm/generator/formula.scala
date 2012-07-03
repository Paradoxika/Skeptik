package skeptik.algorithm.generator

import skeptik.expression.E
import skeptik.expression.formula.{Prop, Imp}
import util.Random

object FormulaGenerator {
  private val atoms = Seq("A","B","C","D","E","F","G","H","I","J","K").map(Prop(_))
 
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
        if (i == 1) List(Prop("A"))
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
    
    def growLists(lists: Seq[List[E]]) = (for (l <- lists.view) yield {
      val numOfSymbolsInList = l.distinct.length
      val numOfSymbolsToTake = if (numOfSymbolsInList < numOfSymbols) numOfSymbolsInList + 1 else numOfSymbols
      for (a <- atoms.take(numOfSymbolsToTake).view) yield a::l        
    }).flatten.filter(l => numOfSymbols - l.distinct.length <= length - l.length)
    
    val lists = {
      def rec(i:Int):Seq[List[E]] = {
        if (i == 1) Seq(List(Prop("A")))
        else {
          val previous = rec(i-1)
          growLists(previous)
        }
      }
      rec(length)
    }
    
    def generateFormulas(l:List[E]):List[E] = {
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
  
  
//  def generate(maxLength: Int, maxSymbols: Int) = {
//    def growLists(lists: Seq[List[E]]): Seq[List[E]]  = {
//      var grownLists = Seq[List[E]]()
//      for (l <- lists.view) {
//        val numberOfSymbolsInList = l.distinct.length
//        val numberOfSymbols = if (numberOfSymbolsInList < maxSymbols) numberOfSymbolsInList + 1 else maxSymbols
//        for (a <- atoms.take(numberOfSymbols).view) grownLists ++= Seq((a::l))
//      }
//      grownLists
//    }
//    
//    val lists = {
//      def rec(i:Int):Seq[List[E]] = {
//        if (i == 1) Seq(List(Prop("A")))
//        else {
//          val previous = rec(i-1)
//          growLists(previous).toSeq
//        }
//      }
//      rec(maxLength)
//    }
//    
//    def generateFormulas(l:List[E]):List[E] = {
//      var formulas = List[E]()
//      if (l.length == 1) formulas = l
//      else for (i <- 1 to l.length - 1) {
//        val left = l.take(i)
//        val right = l.drop(i)
//        val leftFormulas = generateFormulas(left)
//        val rightFormulas = generateFormulas(right)
//        for (lf <- leftFormulas; rf <- rightFormulas) formulas = Imp(lf,rf)::formulas
//      }
//      formulas
//    } 
//    
//    var formulas = Seq[E]()
//    for (l <- lists) formulas ++= generateFormulas(l)
//    
//    formulas
//  }
}